//! The proof ledger: the checked record of which rules were proven, keyed by content hash.

use std::collections::BTreeMap;

use super::RuleId;

/// The proof ledger: one line per rule with its content hash and evidence. Generated, never
/// edited; tests recompute it so it cannot vouch for anything that was not checked.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ledger {
    pub(crate) entries: BTreeMap<String, (String, String, String)>,
}

impl Ledger {
    #[cfg_attr(not(feature = "check"), allow(dead_code))]
    pub(crate) fn from_entries(entries: BTreeMap<String, (String, String, String)>) -> Ledger {
        Ledger { entries }
    }

    pub(crate) const HEADER: &'static str = "# bitwright proof ledger v2. Generated; do not edit.";

    /// Renders the ledger text.
    pub fn render(&self) -> String {
        let mut s = String::from(Self::HEADER);
        s.push('\n');
        for (name, (id, kind, ev)) in &self.entries {
            s.push_str(&format!("{name} {id} {kind} {ev}\n"));
        }
        s
    }

    /// Parses ledger text.
    pub fn parse(text: &str) -> Result<Ledger, String> {
        let mut entries = BTreeMap::new();
        if text.lines().next().map(str::trim) != Some(Self::HEADER) {
            return Err(format!("line 1: expected `{}`", Self::HEADER));
        }
        for (i, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let mut parts = line.splitn(4, ' ');
            let (Some(name), Some(id), Some(kind), Some(ev)) =
                (parts.next(), parts.next(), parts.next(), parts.next())
            else {
                return Err(format!("line {}: malformed entry", i + 1));
            };
            entries.insert(
                name.to_string(),
                (id.to_string(), kind.to_string(), ev.to_string()),
            );
        }
        Ok(Ledger { entries })
    }

    /// Differences between this ledger and `other`, as human-readable lines.
    pub fn diff(&self, other: &Ledger) -> Vec<String> {
        let mut out = Vec::new();
        for (name, e) in &self.entries {
            match other.entries.get(name) {
                None => out.push(format!("{name}: missing from the other ledger")),
                Some(o) if o != e => out.push(format!("{name}: {e:?} vs {o:?}")),
                _ => {}
            }
        }
        for name in other.entries.keys() {
            if !self.entries.contains_key(name) {
                out.push(format!("{name}: only in the other ledger"));
            }
        }
        out
    }

    /// Whether the ledger vouches for this rule: an entry of the rule's content hash, under
    /// its name or any other. The hash is of the normalized rule (its sides, guard and
    /// widths: no names, positions or docs), so the same rule in another file or group, or
    /// renamed, was checked when any spelling of it was.
    pub fn vouches_for(&self, name: &str, id: RuleId) -> bool {
        let id = id.to_string();
        (self.entries.get(name)).is_some_and(|(i, _, _)| *i == id)
            || self.vouches_for_content_text(&id)
    }

    /// Whether some entry is of this content hash.
    pub fn vouches_for_content(&self, id: RuleId) -> bool {
        self.vouches_for_content_text(&id.to_string())
    }

    fn vouches_for_content_text(&self, id: &str) -> bool {
        self.entries.values().any(|(i, _, _)| i == id)
    }

    /// Adds the entries of `other` (ledgers of two rule files as one). An entry of the same
    /// name stays this ledger's.
    pub fn merge(&mut self, other: &Ledger) {
        for (name, e) in &other.entries {
            self.entries
                .entry(name.clone())
                .or_insert_with(|| e.clone());
        }
    }
}
