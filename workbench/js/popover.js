// The node popover: click a subterm anywhere (the expression text, a tree row) and see what the
// run says about it: its width and facts, what was tried at it, the step that made it, the
// steps that rewrote it, with links into the other views.

import { h, fill } from "./dom.js";
import { print } from "./print.js";
import { aboutNode } from "./model.js";
import { factsBlock } from "./cards.js";

const OUTCOME = {
  applied: "applied",
  no_match: "no match",
  guard_false: "guard false",
  degraded: "out of work",
  no_change: "no change",
  not_smaller: "not smaller",
  rejected: "rejected",
  vetoed: "vetoed",
};

let el = null;
let anchor = null;

function root() {
  if (!el) el = document.getElementById("popover");
  return el;
}

/// Shows the popover for node id `id` of `app.run`, under `at` (an element).
export function showNode(app, id, at) {
  const run = app.run;
  const about = aboutNode(run, id);
  const n = about.node;
  if (!n) return;
  const p = root();
  anchor = at;
  const attempts = about.attempts;
  const byOutcome = {};
  for (const a of attempts) byOutcome[a.outcome] = (byOutcome[a.outcome] ?? 0) + 1;
  const go = (tab, extra) => () => {
    hide();
    app.go(tab, extra);
  };
  fill(
    p,
    h(
      "div",
      { class: "pop-head" },
      h("span", { class: "label" }, `node · ${n.w} bit${n.w === 1 ? "" : "s"}`),
      h("button", { class: "x", type: "button", "aria-label": "Close", onclick: hide }, "×"),
    ),
    h("div", { class: "code small pop-expr" }, print(run, id)),
    factsBlock(run, id, "known bits"),
    attempts.length
      ? h(
          "div",
          { class: "pop-sec" },
          h("div", { class: "label" }, `${attempts.length} attempt${attempts.length > 1 ? "s" : ""} here`),
          h(
            "div",
            { class: "pop-att" },
            attempts.slice(0, 8).map((a) => {
              const who = a.type === "rule" ? (run.rules[a.rule]?.name ?? "").split("::").pop() : a.pass;
              return h("div", { class: `pop-a o-${a.outcome}` }, h("span", { class: "o" }, OUTCOME[a.outcome] ?? a.outcome), h("span", { class: "mono" }, who), a.pred ? h("span", { class: "muted" }, ` ${a.pred}`) : null);
            }),
            attempts.length > 8 ? h("div", { class: "muted" }, `+${attempts.length - 8} more`) : null,
          ),
        )
      : h("div", { class: "pop-sec muted" }, "Nothing was tried at this node."),
    about.madeBy || about.rewrittenAt.length
      ? h(
          "div",
          { class: "pop-sec" },
          about.madeBy ? h("div", {}, "made by ", h("button", { class: "link", onclick: go("trace", { step: about.madeBy.index }) }, `step ${about.madeBy.index}`), h("span", { class: "muted" }, ` (${about.madeBy.name.split("::").pop()})`)) : null,
          about.rewrittenAt.length ? h("div", {}, "rewritten at ", about.rewrittenAt.map((s, i) => [i ? ", " : "", h("button", { class: "link", onclick: go("trace", { step: s.index }) }, `step ${s.index}`)])) : null,
        )
      : null,
    h(
      "div",
      { class: "pop-actions" },
      attempts.length ? h("button", { type: "button", onclick: go("whynot", { node: id }) }, "Why not") : null,
      n.facts ? h("button", { type: "button", onclick: go("facts", { node: id }) }, "Facts") : null,
      h("button", { type: "button", onclick: () => { navigator.clipboard?.writeText(print(run, id)).catch(() => {}); hide(); } }, "Copy"),
    ),
  );
  p.hidden = false;
  place(p, at);
}

function place(p, at) {
  const r = at.getBoundingClientRect();
  const pw = p.offsetWidth;
  const ph = p.offsetHeight;
  let x = Math.min(Math.max(8, r.left), window.innerWidth - pw - 8);
  let y = r.bottom + 6;
  if (y + ph > window.innerHeight - 8) y = Math.max(8, r.top - ph - 6);
  p.style.left = `${x}px`;
  p.style.top = `${y}px`;
}

export function hide() {
  const p = root();
  p.hidden = true;
  anchor = null;
}

export function isOpen() {
  return el && !el.hidden;
}

/// Wires the popover to a container: a click on a `.t` span or a `[data-n]` row shows its node;
/// hovering marks the innermost subterm only.
export function wire(app, container) {
  container.addEventListener("click", (e) => {
    const t = e.target.closest("[data-n]");
    if (!t || !container.contains(t)) return;
    if (e.target.closest("a, button.link, button:not(.row)")) return;
    e.stopPropagation();
    const id = Number(t.dataset.n);
    if (isOpen() && anchor === t) {
      hide();
      return;
    }
    showNode(app, id, t);
  });
  let hovered = null;
  container.addEventListener("mouseover", (e) => {
    const t = e.target.closest(".t");
    if (hovered && hovered !== t) hovered.classList.remove("hov");
    hovered = t;
    if (t) t.classList.add("hov");
  });
  container.addEventListener("mouseleave", () => {
    if (hovered) hovered.classList.remove("hov");
    hovered = null;
  });
}

/// Closes on a click outside, on Escape, and when the page scrolls.
export function install() {
  document.addEventListener("click", (e) => {
    if (isOpen() && !root().contains(e.target)) hide();
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && isOpen()) hide();
  });
  document.addEventListener("scroll", () => { if (isOpen()) hide(); }, true);
}

