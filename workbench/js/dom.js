// A small element builder: `h("div", { class: "x", onclick }, child, "text", …)`.

export function h(tag, attrs = {}, ...kids) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs ?? {})) {
    if (v === undefined || v === null || v === false) continue;
    if (k === "class") el.className = v;
    else if (k === "html") el.innerHTML = v;
    else if (k === "text") el.textContent = v;
    else if (k === "style" && typeof v === "object") Object.assign(el.style, v);
    else if (k.startsWith("on") && typeof v === "function") el.addEventListener(k.slice(2), v);
    else if (v === true) el.setAttribute(k, "");
    else el.setAttribute(k, String(v));
  }
  append(el, kids);
  return el;
}

function append(el, kids) {
  for (const c of kids) {
    if (c === undefined || c === null || c === false) continue;
    if (Array.isArray(c)) append(el, c);
    else if (c instanceof Node) el.appendChild(c);
    else el.appendChild(document.createTextNode(String(c)));
  }
}

/// Replaces an element's content.
export function fill(el, ...kids) {
  el.replaceChildren();
  append(el, kids);
  return el;
}

/// The colour class of a step or maker kind.
export function kindClass(kind) {
  return `k k-${kind}`;
}

/// A chip: `chip("rule", "core.arith::mul_pow2")`.
export function chip(kind, text, plain = false) {
  return h("span", { class: `chip ${kindClass(kind)}${plain ? " plain" : ""}` }, text);
}

/// A key/value list.
export function kv(pairs) {
  const dl = h("dl", { class: "kv" });
  for (const [k, v] of pairs) {
    if (v === undefined || v === null || v === "") continue;
    dl.append(h("dt", {}, k), h("dd", {}, v));
  }
  return dl;
}
