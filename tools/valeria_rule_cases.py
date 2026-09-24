#!/usr/bin/env python3
"""Emit bounded Bitwright probes from the committed Valeria rule corpus.

This is a coverage inventory, not a proof or a rule exporter. Unknown guards,
host queries and unsupported operators are recorded as skips, never assumed.
Run the emitted TSV through Bitwright's `valeria_rule_audit` example. Keep its
before/after output when porting a rule; never replace evidence with rule counts.
"""
import argparse
import collections
import json
from pathlib import Path
import re


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
            raise Refusal("known-bits-query")
        values = [self.meta(a) for a in args]
        if op == "popcnt_meta":
            return values[0].bit_count()
        if op == "bsf_meta" and values[0]:
            return (values[0] & -values[0]).bit_length()
        operations = {"meta_add": lambda a,b:a+b, "meta_sub": lambda a,b:a-b,
                      "meta_mul": lambda a,b:a*b, "meta_and": lambda a,b:a&b,
                      "meta_or": lambda a,b:a|b, "meta_mod": lambda a,b:a%b,
                      "meta_shl": lambda a,b:a<<b, "meta_shr": lambda a,b:a>>b,
                      "meta_not": lambda a:(~a)&((1<<128)-1)}
        if op not in operations:
            raise Refusal("meta:" + op)
        if any(abs(v) > 512 for v in values[1:]) and op in ("meta_shl", "meta_shr"):
            raise Refusal("meta-shift-budget")
        return operations[op](*values) & ((1 << 128) - 1)

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
        raise Refusal("symbolic-guard:" + op)

    def expr(self, node, hint=None):
        op, args = node
        width = hint or self.width
        if op.startswith("$"):
            width = self.width
            value = self.bindings.get(op)
            return self.number(value, width) if value is not None else (op[1:], width, None)
        if re.fullmatch(r"-?\d+", op):
            return self.number(int(op), width)
        if op == "iff":
            if not self.guard(args[0]):
                raise Refusal("guard-false")
            return self.expr(args[1], hint)
        if op in ("simplify", "try_simplify"):
            return self.expr(args[0], hint)
        if op == "lit_meta":
            return self.number(self.meta(args[0]), width)
        if op in ("ucast", "cast"):
            a, aw, av = self.expr(args[0])
            target = self.expr(args[1])[2]
            if target is None or not 1 <= target <= 64:
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
            if aw != bw:
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
            # Preserve Valeria's ISA count masking explicitly in coverage probes.
            mask = 63 if aw == 64 else 31
            b = f"(({b}) & {mask}:{bw})"
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
            if cw != 1 or yw != nw:
                raise Refusal("select-width")
            return f"select({condition}, {yes}, {no})", yw, None if cv is None else yv if cv else nv
        if op in ("clz", "popcnt", "pdep", "pext", "umin", "umax", "smin", "smax"):
            values = [self.expr(a, hint) for a in args]
            return f"{op}({', '.join(v[0] for v in values)})", values[0][1], None
        raise Refusal("operator:" + op)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rules", type=Path, required=True, help="Valeria valeria-symex/rules-src directory")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--widths", default="8,16,32,64")
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
            for width in map(int, opts.widths.split(',')):
                mask = (1<<width)-1
                profiles = [dict(), {"$b":0,"$c":1}, {"$b":1,"$c":0},
                            {"$b":1,"$c":1}, {"$b":mask,"$c":0},
                            {"$b":1<<(width-1),"$c":mask}]
                for index, values in enumerate(profiles):
                    values = {key: value for key, value in values.items() if key not in nonconstants}
                    values.update({slot:[0,1,2,mask,mask>>1,width-1][index] for slot in constants})
                    instance = Instance(width, values)
                    try:
                        left, lw, _ = instance.expr(parse(lhs))
                        right, rw, _ = instance.expr(parse(rhs), lw)
                        if lw != rw:
                            raise Refusal("result-width")
                        key = width, left, right
                        if key not in seen:
                            seen.add(key)
                            cases.append(f"{rule}/{index}\t{width}\t{left}\t{right}")
                            count += 1
                    except (Refusal, KeyError, ZeroDivisionError) as error:
                        reasons[str(error)] += 1
            inventory.append(dict(rule=rule, cases=count, skipped=dict(reasons)))
    opts.output.write_text('\n'.join(cases)+'\n', encoding='utf-8')
    opts.inventory.write_text(json.dumps(inventory,indent=2)+'\n',encoding='utf-8')
    print(f"{len(inventory)} rules; {sum(row['cases']>0 for row in inventory)} with probes; {len(cases)} cases")


if __name__ == "__main__":
    main()
