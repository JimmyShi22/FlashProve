-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Send.lean: the sending of a family of oracle messages, as one kind of block: the reduction,
its joints, the statement that it is knowledge sound, and what is proved beside that statement.

A chain of a key file is made of blocks of a few kinds. For each kind there is one statement,
general in the block's sizes, that the block is round-by-round knowledge sound between its own
joints. This file has the kind "send": the prover sends the words of several oracle messages as one
oracle, the verifier answers with one joint seed, and the prover sends each message's answers in the
clear. The reduction is the library's `ldSendFam` (Cb/Ld/LdSendFam.lean); nothing of it is stated
anew. The file imports no file of the program.

  `Size`      what is public of a sending: the family N of oracle messages (their codes, formats and
              samples), how the members' seeds are drawn from the joint seed (Sd), and for each
              member a bound L on the length of a list of close codewords.
  `R`, `eps`  the reduction, two rounds; its errors: the first round's is the sum over the members a
              of mult a * (L a choose 2) * (the sample's error), a count of joint seeds; the
              second's is 0.
  `outJ`      the joint after the sending, for a joint A before it: each sent word decodes, with its
              sample, to the witness's message of that member, and A is claimed of what `back` makes
              of these messages and the further witness. Statements at which a member has a
              collision are let in, and every witness counts for them (`IOR.Rels.cf`,
              Ior/KnowCollGood.lean).
  `HAt s`     the statement at the size s. All that is still a letter is bound inside: the types of
              cores, statements and witnesses, the further oracles, the joint A before the sending,
              and `back`. It says: the reduction is knowledge sound (`Reduction.Know`) on the
              statements of A, from A's relaxed relation to that of `outJ`, with the extractor
              "`back` of the messages", at `eps s`.
  `hAt`       the statement holds if the seeds are fair, the lists are bounded by L, and the samples
              evade: the library's `ldSendFam_into`.
  `Size.OK`, `hAt_of_ok`   these three conditions and the codes' laws as one record; they speak of
              public data alone.
  `H sizes`, `h_of_ok`   the statement at every size of a list; it holds if every size of the list
              meets `Size.OK`.
  `ofSendD`, `ofSendD_ok`   the size of a sending of the library's segments (`LdSendD`,
              Cb/Req1/LdSegKit.lean); it meets `Size.OK` if and only if the sending meets
              `LdSendD.HypK` (Cb/Thin/Kinds/Send.lean).
  Beside it, for all sizes: `point`, `isLocal` (if the members' codes meet their laws), `onOut`;
  `passes` (the statement before is handed on), `copies` (the oracles before are handed on),
  `never_rejects`; `rounds`, `errs`, `vals`: two rounds, the two errors, the numbers of values of
  the verifier's messages.

Not shown here. That a family of a key file's chains meets the conditions. (In the library: `Fair`
of a built family: `bld_fair`, Cb/Ld/LdBldMsg.lean; `ListLE` from a bound on the code's lists and
`Evades` from the sample's law: `sig_list_of_code`, `sig_evades_of_ok`, Cb/Ld/LdSig.lean; the codes'
laws and the bounds on lists are the caller's there.) That the errors are a plan's bounds. Anything
on an honest prover.
Limits: the output joint is nested: A stands inside the joint over N. It is the input joint of the
round before a proximity test only where N is that round's whole family (`send_bat_seam`,
Cb/Pv/Bat.lean); behind two sendings the library's way is one grown family (`LdSendD.link`; its
knowledge soundness alone: `LdSendD.goodK`, Cb/Thin/Kinds/Send.lean). An oracle without a sample
that goes in the same prover message for a later block (a rider) is not treated here: a sending
whose first message bears a rider is in Cb/Pv/SendRide.lean [not in this library]. The errors are
bare counts for one instance: nothing on proof of work, nothing on several instances.

-/
import Cb.Ld.LdSendFamProofs
import Cb.Ld.LdWfPre
import Ior.KnowCollRulesChainErr
import Cb.Req1.LdSegKit
import Cb.Thin.Kinds.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Send
open Iop IOR Cb

/-- What is public of a sending. -/
structure Size (E : Type) where
  /-- the family of oracle messages -/
  N : Sig E
  /-- how the members' seeds are drawn -/
  Sd : N.Seeds
  /-- for each member a bound on the length of a list -/
  L : N.O → ℕ

variable {E : Type} [Field E] (s : Size E)

/-- The reduction. -/
noncomputable def R (X : Type) (E₀ : ExtSpec) : IOR X E₀ (X × s.N.Smp) (E₀.prod s.N.ext) :=
  ldSendFam s.N s.Sd X E₀

/-- The errors. -/
def eps : Err (s.N.sh s.Sd) := (ldSendFamErr s.N s.Sd s.L, (0, ()))

/-- The joint after the sending. -/
def outJ {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W) (back : s.N.Msg → W' → W) :
    Rels Kc (X × s.N.Smp) (E₀.prod s.N.ext) (s.N.Wit × W') :=
  (s.N.over (s.N.pull A back)).cf

/-- The statement that the sending at the size s is knowledge sound. -/
def HAt : Prop :=
  ∀ (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W) (back : s.N.Msg → W' → W),
    (R s X E₀).red.Know A.on A.relR (outJ s A back).relR
      (fun _ _ w => back (s.N.msgs w.1) w.2) (eps s)

/-- The statement holds if the seeds are fair, the lists are bounded and the samples evade. -/
theorem hAt (hF : s.Sd.Fair) (hl : ∀ a, (s.N.om a).ListLE (s.L a))
    (hE : ∀ a, (s.N.om a).Evades) : HAt s :=
  fun Kc X W W' E₀ A back => ldSendFam_into E s.N s.Sd Kc X W W' E₀ A back s.L hF hl hE

/-- The conditions, on public data alone. -/
structure Size.OK (s : Size E) : Prop where
  laws   : ∀ a, (s.N.om a).C.Laws
  fair   : s.Sd.Fair
  list   : ∀ a, (s.N.om a).ListLE (s.L a)
  evades : ∀ a, (s.N.om a).Evades

theorem hAt_of_ok (h : s.OK) : HAt s := hAt s h.fair h.list h.evades

/-- The statement at every size of a list. -/
def H (sizes : List (Size E)) : Prop := ∀ s ∈ sizes, HAt s

theorem h_of_ok (sizes : List (Size E)) (h : ∀ s ∈ sizes, s.OK) : H sizes :=
  fun s hs => hAt_of_ok s (h s hs)

/-- The size of a sending of the library's segments. -/
def ofSendD {Kc : Type} {a : LdStage E Kc} (d : LdSendD a) : Size E := ⟨d.N, d.Sd, d.L⟩

/-- The two records of conditions are one. -/
theorem ofSendD_ok {Kc : Type} {a : LdStage E Kc} (d : LdSendD a) : (ofSendD d).OK ↔ d.HypK :=
  ⟨fun h => ⟨h.laws, h.fair, h.list, h.evades⟩, fun h => ⟨h.laws, h.fair, h.list, h.evades⟩⟩

/-! ### beside the statement, for all sizes -/

theorem point (X : Type) (E₀ : ExtSpec) : Nonempty (R s X E₀).shape.IsPoint := ⟨s.N.pt s.Sd⟩

theorem isLocal (X : Type) (E₀ : ExtSpec) (hL : ∀ a, (s.N.om a).C.Laws) : (R s X E₀).IsLocal :=
  ldSendFam_isLocal s.N s.Sd X E₀ hL

theorem onOut {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W) (back : s.N.Msg → W' → W) :
    ∀ a τ b, A.on a → (R s X E₀).red.out a τ = some b → (outJ s A back).on b :=
  fun _ _ _ _ _ => trivial

/-- The statement before the sending is handed on. -/
theorem passes (X : Type) (E₀ : ExtSpec) : (R s X E₀).Passes id Prod.fst := by
  intro x y τ x' h
  have h' : some (x, fun a => (s.Sd.sd a τ.2.1, τ.2.2.1.2 a)) = some x' := h
  rw [← Option.some.inj h']
  rfl

/-- The oracles before the sending are handed on. -/
theorem copies (X : Type) (E₀ : ExtSpec) (y : E₀.Str) (τ : Tr (R s X E₀).shape) :
    ((R s X E₀).imp y τ).1 = y := rfl

/-- The verifier never rejects. -/
theorem never_rejects (X : Type) (E₀ : ExtSpec) (x : X) (y : E₀.Str) (τ : Tr (R s X E₀).shape) :
    ((R s X E₀).out x y τ).isSome := rfl

theorem rounds (X : Type) (E₀ : ExtSpec) : (R s X E₀).shape.length = 2 := rfl

theorem errs : (eps s).toList = [ldSendFamErr s.N s.Sd s.L, 0] := rfl

theorem vals (X : Type) (E₀ : ExtSpec) :
    (R s X E₀).shape.chalList = [Fintype.card s.Sd.D, 1] := rfl

#print axioms hAt_of_ok
#print axioms isLocal
#print axioms ofSendD_ok

end Cb.Pv.Send
