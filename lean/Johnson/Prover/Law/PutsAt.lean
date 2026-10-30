-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/PutsAt.lean: AT THE WIRE RECORD OF A WHOLE WRITTEN FILE THE NUMBERS THAT A SEARCH
TRIES ARE WRITTEN APART, AT EVERY CAP: PutsApart (Johnson/Prover/Law/Defs.lean) at wqWhole
(OnBytes/Maker/Wire.lean), for all caps and from every round number.

Why. The wire record's own law (GrW.OK.get_put, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) says that the
numbers up to "more" are read back; at the written files "more" is 65,535 (Run.PQ.Dn,
Run/PlanQWire.lean:137). The compiled prover of OnBytes/Prover/Defs.lean does not read "more": its
caps are arguments, and the law of its outcome wants caps far above that number. At the written
files a nonce IS its number (Dn's enc is the identity on ℕ): so all numbers are written apart.

Main names.
  PutsFree   every record of every round writes all numbers apart: no cap, no round number.
  putsApart_of_free   so PutsApart at all caps, from every round number.
  putsFree_app   it goes through WireSB.app (OnBytes/TypedOracleCompiler/Joined/Cut.lean).
  grApart_Dn   a record that is made by grOf at Dn writes all numbers apart.
  putsFree_wiresLo, putsFree_wiresSh   the written rounds, local and shared.
  putsFree_wqWhole, putsApart_wqWhole   THE STATEMENT.

Limits. In Lean a nonce of these records is a natural number. IN A FILE A NONCE HAS EIGHT BYTES (so
Fmt/M3ParOfLaws.lean's head says of the entry file at the programs' own sizes; of the other two
files this is read, not shown here): that a number from 2^64 on
cannot be written into a file is no matter of this record and is not said here: whoever goes to
bytes bounds the caps. The entry file's wire (wSib) is not spoken of. That a description's wire is
wqWhole: wireFullK (Johnson/Flat/WireAt.lean), not called here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Defs
import OnBytes.Maker.Wire

set_option autoImplicit false

namespace OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {lam K : ℕ}

/-- Every record of every round writes all numbers apart. -/
def PutsFree : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) =>
      (∀ g, w.grJ = some g → ∀ cap, GrApart g cap) ∧
        (∀ g, w.gr0 = some g → ∀ cap, GrApart g cap) ∧ PutsFree s A W

theorem putsApart_of_free : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    PutsFree s A W → ∀ (cap : ℕ → ℕ) (i : ℕ), PutsApart s A W cap i
  | [], _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), h, cap, i => by
    refine ⟨?_, putsApart_of_free s A W h.2.2 cap (i + 1)⟩
    cases a.kind with
    | lo => exact fun g hg => h.1 g hg (cap i)
    | sh => exact fun g hg => h.2.1 g hg (cap i)

theorem putsFree_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, PutsFree s A W → PutsFree u B V →
      PutsFree (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, hW.2.1, putsFree_app hW.2.2 hV⟩

/-- **A record that is made by grOf at Dn writes all numbers apart**: a nonce is its number. -/
theorem grApart_Dn {C P : Type} : ∀ (b : ℕ) (g : GrW (GChal b C) (GPlain ℕ b P)),
    (grOf Dn C P b).map TypedOracleCompiler.Tagged.ofGr = some g → ∀ cap, GrApart g cap
  | 0, _, h => by cases h
  | b + 1, g, h => by
    obtain rfl : TypedOracleCompiler.Tagged.ofGr (_root_.Iop.GrW.ofBits Dn b C P) = g := Option.some.inj h
    intro cap α n n' _ _ e
    have e' : ((GPlain.old α, n) : P × ℕ) = (GPlain.old α, n') := e
    exact (Prod.mk.inj e').2

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem putsFree_wiresLo : ∀ ds : List RDT, PutsFree _ _ (wiresLo C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨fun g hg => grApart_Dn _ g hg, (fun _ hg => by cases hg), putsFree_wiresLo ds⟩

theorem putsFree_wiresSh : ∀ ds : List RDT, PutsFree _ _ (wiresSh C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨(fun _ hg => by cases hg), fun g hg => grApart_Dn _ g hg, putsFree_wiresSh ds⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **At the wire record of a whole written file every record writes all numbers apart.** -/
theorem putsFree_wqWhole : PutsFree _ _ (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg),
    putsFree_app (putsFree_wiresLo C K chal D.ds₁)
      ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg),
        putsFree_app (putsFree_wiresSh C K chal D.ds₂)
          ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg), putsFree_wiresLo C K chal D.ds₃⟩⟩⟩

/-- **So PutsApart there, at all caps and from every round number.** -/
theorem putsApart_wqWhole (cap : ℕ → ℕ) (i : ℕ) :
    PutsApart _ _ (wqWhole C K chal D tF tJ t3 silent run).sh cap i :=
  putsApart_of_free _ _ _ (putsFree_wqWhole C K chal D tF tJ t3 silent run) cap i

end

end OnBytes.Prover

#print axioms OnBytes.Prover.putsApart_of_free
#print axioms OnBytes.Prover.putsFree_app
#print axioms OnBytes.Prover.grApart_Dn
#print axioms OnBytes.Prover.putsFree_wiresLo
#print axioms OnBytes.Prover.putsFree_wiresSh
#print axioms OnBytes.Prover.putsFree_wqWhole
#print axioms OnBytes.Prover.putsApart_wqWhole
