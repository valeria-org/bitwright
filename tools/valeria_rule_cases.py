#!/usr/bin/env python3
"""Emit bounded Bitwright probes from the committed Valeria rule corpus.

This is a coverage inventory, not a proof or a rule exporter. Unknown guards,
host queries and unsupported operators are recorded as skips, never assumed.
Run the emitted TSV through Bitwright's `valeria_rule_audit` example. Keep its
before/after output when porting a rule; never replace evidence with rule counts.
"""
import argparse
import collections
from dataclasses import dataclass
import json
from pathlib import Path
import re


@dataclass(frozen=True)
class Binding:
    text: str
    width: int
    one: int = 0
    zero: int = 0
    value: int | None = None


def masked(name, width, free, one=0):
    mask = (1 << width) - 1
    free &= mask & ~one
    one &= mask
    return Binding(f"(({name}:{width} & {free}:{width}) | {one}:{width})",
                   width, one, mask & ~(free | one), one if not free else None)


class Refusal(Exception):
    pass


def parse(text):
    text = re.sub(r":\s*bv<[^>]+>(?:\s+(?:constant|nonconstant))?", "", text)
    tokens = re.findall(r"\$\w+|-?\d+|\w+|[(),]", text)
    cursor = 0

    def take():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if cursor < len(tokens) and tokens[cursor] == "(":
            cursor += 1
            args = []
            while tokens[cursor] != ")":
                args.append(take())
                if tokens[cursor] == ",":
                    cursor += 1
                elif tokens[cursor] != ")":
                    raise Refusal("syntax")
            cursor += 1
            return token, args
        return token, []

    result = take()
    if cursor != len(tokens):
        raise Refusal("syntax")
    return result


COMPARE = {"eq": "==", "ne": "!=", "ult": "<u", "ule": "<=u", "ugt": ">u",
           "uge": ">=u", "slt": "<s", "sle": "<=s", "sgt": ">s", "sge": ">=s"}
INFIX = {"add": "+", "sub": "-", "mul": "*", "and": "&", "or": "|", "xor": "^"}


class Instance:
    def __init__(self, width, bindings):
        self.width, self.bindings = width, bindings

    def number(self, value, width):
        value &= (1 << width) - 1
        return f"{value}:{width}", width, value

    def meta(self, node):
        op, args = node
        if re.fullmatch(r"-?\d+", op):
            return int(op)
        if op == "bcnt":
            return self.expr(args[0])[1]
        if op == "value":
            value = self.expr(args[0])[2]
            if value is not None:
                return value
            raise Refusal("symbolic-value-guard")
        if op in ("mask_known_one", "mask_known_zero", "mask_unknown"):
            zero, one, width = self.bits(args[0])
            return {"mask_known_one": one, "mask_known_zero": zero,
                    "mask_unknown": ((1 << width) - 1) & ~(zero | one)}[op]
        values = [self.meta(a) for a in args]
        if op == "popcnt_meta":
            return values[0].bit_count()
        if op == "bsf_meta" and values[0]:
            return (values[0] & -values[0]).bit_length()
        operations = {"meta_add": lambda a,b:a+b, "meta_sub": lambda a,b:a-b,
                      "meta_mul": lambda a,b:a*b, "meta_and": lambda a,b:a&b,
                      "meta_or": lambda a,b:a|b, "meta_mod": lambda a,b:a%b,
                      "meta_shl": lambda a,b:0 if b >= 128 else a<<b, "meta_shr": lambda a,b:0 if b >= 128 else a>>b,
                      "meta_not": lambda a:(~a)&((1<<128)-1)}
        if op not in operations:
            raise Refusal("meta:" + op)
        return operations[op](*values) & ((1 << 128) - 1)

    def bits(self, node):
        op, args = node
        text, width, value = self.expr(node)
        mask = (1 << width) - 1
        if value is not None:
            return mask ^ value, value, width
        if op.startswith("$") and isinstance(self.bindings.get(op), Binding):
            value = self.bindings[op]
            return value.zero, value.one, width
        if op in ("simplify", "try_simplify"):
            return self.bits(args[0])
        if op in ("not", "neg"):
            zero, one, _ = self.bits(args[0])
            if op == "not":
                return one, zero, width
            # Sound bitwise addition for ~x + 1, with a set of possible carries.
            out_zero = out_one = 0
            carries = {1}
            for bit in range(width):
                choices = [0] if one & (1 << bit) else [1] if zero & (1 << bit) else [0, 1]
                sums = {v + carry for v in choices for carry in carries}
                values = {v & 1 for v in sums}
                if values == {0}: out_zero |= 1 << bit
                if values == {1}: out_one |= 1 << bit
                carries = {v >> 1 for v in sums}
            return out_zero, out_one, width
        return 0, 0, width

    def guard(self, node):
        op, args = node
        if op == "guard_and":
            return self.guard(args[0]) and self.guard(args[1])
        if op == "guard_or":
            return self.guard(args[0]) or self.guard(args[1])
        if op.startswith("meta_"):
            a, b = (self.meta(arg) for arg in args)
            return {"meta_eq": a==b, "meta_ne": a!=b, "meta_lt": a<b,
                    "meta_le": a<=b, "meta_gt": a>b, "meta_ge": a>=b}[op]
        if op == "expr_cmp":
            result = self.expr((args[0][0], args[1:]))[2]
            if result is not None:
                return bool(result)
            if args[0][0] in ("eq", "ne"):
                az, ao, _ = self.bits(args[1])
                bz, bo, _ = self.bits(args[2])
                if (az & bo) or (bz & ao):
                    return args[0][0] == "ne"
        raise Refusal("symbolic-guard:" + op)

    def expr(self, node, hint=None):
        op, args = node
        width = hint or self.width
        if op.startswith("$"):
            width = self.width
            value = self.bindings.get(op)
            if isinstance(value, Binding):
                return value.text, value.width, value.value
            return self.number(value, width) if value is not None else (op[1:], width, None)
        if re.fullmatch(r"-?\d+", op):
            return self.number(int(op), width)
        if op == "iff":
            if not self.guard(args[0]):
                raise Refusal("guard-false")
            return self.expr(args[1], hint)
        if op in ("simplify", "try_simplify"):
            return self.expr(args[0], hint)
        if op == "choice":
            for alternative in args:
                try:
                    return self.expr(alternative, hint)
                except Refusal:
                    pass
            raise Refusal("no-choice")
        if op == "lit_meta":
            return self.number(self.meta(args[0]), width)
        if op in ("ucast", "cast"):
            a, aw, av = self.expr(args[0])
            target = self.expr(args[1])[2]
            if target is None or not 1 <= target <= 128:
                raise Refusal("cast-width")
            if aw == target:
                return a, aw, av
            kind = "trunc" if target < aw else "sext" if op == "cast" else "zext"
            if av is not None and kind == "sext" and av & (1 << (aw-1)):
                av -= 1 << aw
            return f"{kind}<{target}>({a})", target, None if av is None else av & ((1<<target)-1)
        if op in ("not", "neg"):
            a, aw, av = self.expr(args[0], hint)
            value = None if av is None else ((~av if op == "not" else -av) & ((1<<aw)-1))
            if value is not None:
                return self.number(value, aw)
            return f"{'~' if op == 'not' else '-'}({a})", aw, value
        if op in INFIX or op in COMPARE or op in ("shl", "shr", "sar", "rol", "ror"):
            a, aw, av = self.expr(args[0], hint)
            b, bw, bv = self.expr(args[1], aw)
            if op == "sar" and (aw > 64 or aw != bw):
                raise Refusal("unsupported-legacy-sar")
            if aw != bw and op not in ("shl", "shr", "sar", "rol", "ror"):
                raise Refusal("mixed-width")
            if op in COMPARE:
                if av is None or bv is None:
                    value = int(op in ("eq", "ule", "uge", "sle", "sge")) if a == b else None
                else:
                    if op.startswith("s"):
                        av = av-(1<<aw) if av & (1<<(aw-1)) else av
                        bv = bv-(1<<bw) if bv & (1<<(bw-1)) else bv
                    value = int({"eq":av==bv,"ne":av!=bv,"ult":av<bv,"ule":av<=bv,
                        "ugt":av>bv,"uge":av>=bv,"slt":av<bv,"sle":av<=bv,"sgt":av>bv,"sge":av>=bv}[op])
                return f"(({a}) {COMPARE[op]} ({b}))", 1, value
            if op in INFIX:
                value = None if av is None or bv is None else {
                    "add":lambda:av+bv,"sub":lambda:av-bv,"mul":lambda:av*bv,
                    "and":lambda:av&bv,"or":lambda:av|bv,"xor":lambda:av^bv}[op]() & ((1<<aw)-1)
                return f"(({a}) {INFIX[op]} ({b}))", aw, value
            # Normalize the ISA count before resizing it to Bitwright's width.
            # Narrowing first can change a count, especially for 1-bit operands.
            mask = 127 if aw > 64 else 63 if aw == 64 else 31
            if aw == bw:
                encoded_mask = self.number(mask, bw)[0]
                b = f"(({b}) & {encoded_mask})"
            elif bv is not None:
                count = bv & mask
                count = count % aw if op in ("rol", "ror") else min(count, aw)
                b = self.number(count, aw)[0]
            else:
                cw = max(aw, bw, 8)
                if cw > bw: b = f"zext<{cw}>({b})"
                b = f"(({b}) & {mask}:{cw})"
                b = f"urem({b}, {aw}:{cw})" if op in ("rol", "ror") else f"umin({b}, {aw}:{cw})"
                if cw > aw: b = f"trunc<{aw}>({b})"
            if op in ("rol", "ror"):
                return f"{'rotl' if op == 'rol' else 'rotr'}({a}, {b})", aw, None
            symbol = {"shl":"<<","shr":">>u","sar":">>s"}[op]
            return f"(({a}) {symbol} {b})", aw, None
        if op in ("if", "select"):
            if len(args) not in (2, 3):
                raise Refusal("select-arity")
            condition, cw, cv = self.expr(args[0])
            yes, yw, yv = self.expr(args[1], hint)
            no, nw, nv = self.expr(args[2], yw) if len(args) == 3 else self.number(0, yw)
            if yw != nw:
                raise Refusal("select-width")
            if cw != 1:
                condition = f"(({condition}) != 0:{cw})"
            # Legacy If/Select have nonzero truthiness; they are not low-bit tests.
            result_width = max(cw, yw) if len(args) == 2 else yw
            if result_width > yw:
                yes, no = f"zext<{result_width}>({yes})", f"zext<{result_width}>({no})"
            return f"select({condition}, {yes}, {no})", result_width, None if cv is None else yv if cv else nv
        if op == "bit_test":
            value, width, _ = self.expr(args[0])
            _, _, count = self.expr(args[1])
            if count is None:
                raise Refusal("symbolic-bit-index")
            count &= 127 if width > 64 else 63
            return (f"extract<{count},1>({value})", 1, None) if count < width else self.number(0, 1)
        if op in ("udiv", "urem", "sdiv", "srem"):
            a, aw, _ = self.expr(args[0])
            b, bw, divisor = self.expr(args[1])
            if aw != bw or divisor is None or divisor == 0:
                raise Refusal("partial-division")
            # Only nonzero fixed divisors cross the partial/total boundary.
            return f"{op}({a}, {b})", aw, None
        if op in ("clz", "popcnt", "pdep", "pext", "umin", "umax", "smin", "smax"):
            values = [self.expr(a, hint) for a in args]
            return f"{op}({', '.join(v[0] for v in values)})", values[0][1], None
        raise Refusal("operator:" + op)


def complete_profiles(width, constants, rhs):
    """Construct symbolic witnesses; never invent a successful guard result."""
    mask = (1 << width) - 1
    profiles = []
    counts = sorted({0, 1, 2, 3, 7, 15, 16, 17, 31, 32, 33, 63, 64, 65, 95, 127,
                     max(0, width-1), width, width+1})
    for value in counts:
        values = {slot: value for slot in constants}
        values.update({"$b": value, "$c": value})
        profiles.append(values)
    for left, right in [(1,0), (0,1), (5,3), (3,5), (17,17), (31,31), (63,63),
                        (127,127), (1,width-1), (width-1,1), (width//2,width-width//2)]:
        profiles.append({"$b":left,"$c":right,"$u":left,"$v":right})
    profiles += [{"$u":width}, {"$u":max(1,width//2)},
                 {"$u":min(128,width*2),"$v":width-1,"$c":width}]
    for k in [1, 3, 15, 255, mask//2]:
        k &= mask
        profiles += [
            {"$a":masked("p",width,mask,k)},
            {"$a":masked("p",width,mask^k)},
            {"$a":masked("p",width,k),"$b":masked("q",width,mask^k)},
            {"$b":masked("q",width,mask,k),"$u":k},
            {"$b":masked("q",width,k),"$u":k},
            {"$b":masked("q",width,k),"$u":mask^k},
            {"$u":k,"$v":mask^k},
        ]
    for shift in [1, 2, 7, 15, 16, 31]:
        if shift < width:
            profiles += [{"$b":masked("q",width,(1<<shift)-1),"$u":shift},
                         {"$u":1<<shift,"$c":shift}, {"$b":shift,"$u":1}]
    for u in [1, mask]:
        profiles.append({"$a":masked("p",width,1),"$u":u})
    if width >= 3:
        positive = [masked(name,width,mask^3,1) for name in ("p","q")]
        negative = [Binding(f"-({value.text})",width,one=3) for value in positive]
        for left,right in [(positive[0],positive[1]),(negative[0],negative[1]),
                           (negative[0],0),(positive[0],0)]:
            profiles.append({"$w":left,"$b":right})

    def aliases(node, values):
        op,args=node
        # Construct d to be exactly the guarded value, including its actual width.
        if op == "expr_cmp" and args[0][0] == "eq" and args[2][0] == "$d":
            instance=Instance(width,values)
            text,bits,value=instance.expr(args[1])
            values["$d"]=Binding(text,bits,value=value)
        for child in args:
            aliases(child,values)

    for values in profiles:
        for slot in constants: values.setdefault(slot, 1)
        try:
            aliases(rhs,values)
        except Refusal:
            continue
        yield values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rules", type=Path, required=True, help="Valeria valeria-symex/rules-src directory")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--widths", default="8,16,32,64")
    parser.add_argument("--complete", action="store_true", help="Exercise formerly skipped guards and widths")
    opts = parser.parse_args()
    root = opts.rules
    cases, inventory = [], []
    for source in sorted(root.rglob("*.vrl")):
        for match in re.finditer(r"rule ([^<]+)<[^\n]+> \{\n(.*?)\n\}", source.read_text(), re.S):
            rule, body = match.groups()
            lhs = re.search(r"  match (.*);", body)[1]
            rhs = re.search(r"  replace (.*);", body)[1]
            nonconstants = set(re.findall(r"(\$\w+): bv<[^>]+> nonconstant\b", lhs))
            constants = re.findall(r"(\$\w+): bv<[^>]+> constant\b", lhs)
            reasons, count = collections.Counter(), 0
            seen = set()
            pattern, template = parse(lhs), parse(rhs)

            def offer(width, values, tag):
                nonlocal count
                # A constant cannot witness a NonConstant pattern parameter.
                if any(isinstance(values.get(slot), int) or
                       (isinstance(values.get(slot), Binding) and values[slot].value is not None)
                       for slot in nonconstants):
                    return
                instance = Instance(width, values)
                try:
                    left, lw, _ = instance.expr(pattern)
                    right, rw, _ = instance.expr(template, lw)
                    if lw != rw:
                        raise Refusal("result-width")
                    key = width, left, right
                    if key not in seen:
                        seen.add(key)
                        cases.append(f"{rule}/{tag}\t{width}\t{left}\t{right}")
                        count += 1
                except (Refusal, KeyError, ZeroDivisionError) as error:
                    reasons[str(error)] += 1

            for width in map(int, opts.widths.split(',')):
                mask = (1<<width)-1
                profiles = [dict(), {"$b":0,"$c":1}, {"$b":1,"$c":0},
                            {"$b":1,"$c":1}, {"$b":mask,"$c":0},
                            {"$b":1<<(width-1),"$c":mask}]
                for index, values in enumerate(profiles):
                    values = {key: value for key, value in values.items() if key not in nonconstants}
                    values.update({slot:[0,1,2,mask,mask>>1,width-1][index] for slot in constants})
                    offer(width, values, str(index))
            if opts.complete and count == 0:
                for width in [1,2,8,16,32,33,40,63,64,65,96,127,128]:
                    for index, values in enumerate(complete_profiles(width,constants,template)):
                        offer(width, values, f"guard-{index}")
            inventory.append(dict(rule=rule, cases=count, skipped=dict(reasons)))
    opts.output.write_text('\n'.join(cases)+'\n', encoding='utf-8')
    opts.inventory.write_text(json.dumps(inventory,indent=2)+'\n',encoding='utf-8')
    if opts.complete and any(not row["cases"] for row in inventory):
        raise SystemExit("incomplete rule inventory; inspect zero-case entries")
    print(f"{len(inventory)} rules; {sum(row['cases']>0 for row in inventory)} with probes; {len(cases)} cases")


if __name__ == "__main__":
    main()
