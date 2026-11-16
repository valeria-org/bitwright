//! The threads Bitwright starts for itself.

/// The stack of a thread Bitwright starts (a batch's, a phase run's, an exhaustive sample's, a
/// solver's). Its passes recurse through expressions as deep as the caller builds them: the
/// demanded-bits pass went about 950 frames deep on a sum a VM built, past a spawned thread's
/// default 2 MiB. Reserved, and committed only as deep as a run goes; smaller where addresses
/// have 32 bits. A caller that runs Bitwright on threads of its own gives them as much.
pub(crate) const STACK: usize = if cfg!(target_pointer_width = "64") {
    512 << 20
} else {
    16 << 20
};

/// A thread with [`STACK`].
pub(crate) fn builder() -> std::thread::Builder {
    std::thread::Builder::new().stack_size(STACK)
}

#[cfg(test)]
mod tests {
    /// A frame as large as a demanded-bits step's, recursed far past a default stack.
    fn deep(n: u32) -> u64 {
        let pad = std::hint::black_box([u64::from(n); 256]);
        if n == 0 {
            pad[7]
        } else {
            deep(n - 1).wrapping_add(pad[n as usize % 256])
        }
    }

    #[test]
    fn a_started_thread_recurses_past_the_default_stack() {
        // 20,000 frames of 2 KiB or more: 40 MiB, twenty times a default thread's stack.
        let got = super::builder().spawn(|| deep(20_000)).map(|h| h.join());
        assert!(matches!(got, Ok(Ok(_))));
    }
}
