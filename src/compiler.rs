//! A simple compiler from policies to cBPF programs.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};

mod block;
mod builder;
mod eval;
mod expr;
mod machine;
mod rule;
mod value;
mod words;

use builder::Builder;
#[allow(unused_imports)]
use machine::Regs;

verus! {

/// Possible errors when compiling a policy to cBPF.
#[verifier::external_derive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CompileError {
    /// The compiled program exceeds the cBPF jump offset limit.
    #[error("compiled program exceeds the cBPF jump offset limit")]
    JmpIdxOverflow,
    /// A syscall signature uses more argument slots than `seccomp_data` provides.
    #[error("syscall signature exceeds the available argument slots")]
    SignatureLayout,
    /// A rule condition needs more than the 16 words of scratch memory.
    #[error("rule condition needs more scratch memory than cBPF has")]
    ScratchOverflow,
}

impl<S: Syscall> Policy<S> {
    /// Compiles the policy into a filter program.
    #[cfg_attr(not(target_os = "linux"), allow(unused))]
    pub(crate) fn to_cbpf(&self) -> (res: Result<Program, CompileError>)
        requires self.wf()
        ensures res matches Ok(prog) ==> {
            // Compiled program is well-formed.
            &&& prog.wf()
            // Compiled program implements the policy on well-formed events.
            &&& forall |data: &[u8]| #[trigger] Event::parse(data) matches Some(ev) ==>
                exists |act: Action| {
                    &&& #[trigger] self.eval(ev, act)
                    &&& prog.eval(data) == Outcome::Return(act.to_ret())
                }
        }
    {
        let mut b = Builder::new();

        // The filter's last resort: the event came from an architecture that the
        // policy leaves out of scope.
        //
        //      ret #act_bad_arch
        b.emit(Instr::Ret(RetVal::K(self.act_bad_arch.exec_to_ret())));

        proof { Builder::lemma_ret(b.rev@, self.act_bad_arch.to_ret()); }

        // One block per architecture token, tried in turn:
        //
        //      <block of the first architecture>
        //      <block of the second architecture>
        //      ...
        let mut i = self.archs.len();
        while i > 0
            invariant
                i <= self.archs@.len(),
                self.wf(),
                b.wf(),
                0 < b.rev@.len(),
                b.rev@[0] is Ret,
                forall |data: &[u8]| Event::parse(data) is Some ==>
                    #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                        self.blocks(Event::of(data), i as int).to_ret()),
            decreases i
        {
            i -= 1;
            let ghost prev = b.rev@;
            let ghost i0 = i as int + 1;
            self.emit_arch_block(&mut b, self.archs[i])?;
            proof {
                assert forall |data: &[u8]| Event::parse(data) is Some implies
                    #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                        self.blocks(Event::of(data), i as int).to_ret()) by {
                    assert(Builder::returns_all(prev, data, prev.len(),
                        self.blocks(Event::of(data), i0).to_ret()));
                }
            }
        }

        let ghost gb = b;
        let prog = b.finish();
        proof {
            gb.lemma_wf(prog);
            assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies
                exists |act: Action| {
                    &&& #[trigger] self.eval(Event::of(data), act)
                    &&& prog.eval(data) == Outcome::Return(act.to_ret())
                } by {
                let act = self.blocks(Event::of(data), 0);
                prog.lemma_run(data);
                assert(prog.instrs@.len() == gb.rev@.len());
                assert(Builder::returns_all(gb.rev@, data, gb.rev@.len(), act.to_ret()));
                assert(Builder::extends(gb.rev@, gb.rev@));
                assert(Builder::returns(gb.rev@, data, gb.rev@.len(), Regs::of(MachineState::init()),
                    act.to_ret()));
                assert(Builder::run(gb.rev@, data, gb.rev@.len(), Regs::of(MachineState::init()))
                    == Outcome::Return(act.to_ret()));
                self.lemma_blocks(Event::of(data), 0);
                assert(prog.eval(data) == Outcome::Return(act.to_ret()));
            }
        }
        Ok(prog)
    }
}

} // verus!
