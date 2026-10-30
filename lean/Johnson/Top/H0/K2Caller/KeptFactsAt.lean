-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptFactsAt.lean: the code switch: THE STRUCTURE `KeptFacts`
(PinKeptJoin.lean: what the join for the kept members' pins asks at a held member) FROM THE LAW's
OWN CONDITION IN FRONT. One theorem: a join of `keptFacts_of` (KeptFactsOf.lean), `hT_of_next`
(KeptFactsMore.lean) and five lemmas of Johnson/G/SwitchSampleTop.lean.

Main names:
  `keptFacts_at`: from: the twelve public clauses (`Pub12`, TopAt.lean) · the invariant on stored
    sample rows · four tests with code (`keptAt`, `keptBitsB`, `keptShapeB`, `storedB`): all of
    which `onTop_of_tests` (OnTopFacts.lean) spends too · the program's test on the public sizes
    (`switchTargetCheck`: every acceptance of the switch gives it) · `Fit` · that the verifier's
    state's statement and the front's hold the same oracle messages (at a later link's switch the
    front has pushed a group: the two statements are not one) · and the table of joints' own five:
    where the kept old message is held, that this tenant is listed, its number, that both copies
    have one number, that every leaf is shown.
Limits. The table's five stay premises (for the first: KeptSeatOf.lean). Nothing on soundness. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.KeptFactsMore
import Johnson.Top.H0.K2Caller.OnTopFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (ShownAt numAt)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (keptBitsB keptShapeB storedB numAt_inj hmem_of hrb_of shape_of hx_of)

variable {r : SwRow} {H : r.OK} {Xi P : Type} (G : FileDescription Xi)
  (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2)
  (orc : Strs → ℕ → ℕ → List UInt64) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))

/-- **`KeptFacts` AT A HELD MEMBER, FROM THE LAW's OWN CONDITION IN FRONT**: the twelve public
clauses, the invariant on stored sample rows and four tests with code (what `onTop_of_tests`
    spends),
the program's test on the public sizes (every acceptance of the switch gives it), `Fit`, and the
table of joints' own five: where the kept old message is held, that this tenant is listed, its
    number,
that both copies have one number, that every leaf is shown. -/
theorem keptFacts_at (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (P12 : Pub12 (r := r) W₀ fx)
    (hchk : switchTargetCheck (K2.skelOf fx) fx.f.rows fx.T = true) (hG : K2.SampleGoodS fx.st)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true)
    (hS : storedB r W₀ fx = true)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ (memK (r := r) (H := H)) rowK (plK W₀))
    (hst : a.2.st.oracles = fx.st.oracles) (k : {a // (plainHd r H).cl a})
    (hseat : KeptSeat G p t fx (orc y) y (keptK2 r H W₀ k).old (r.lo.get k.1.1).1 (seat k.1.1)
      (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a))
    (hlist : seat k.1.1 ∈ seats)
    (hnum : numAt seats ⟨⟨r.lo, seat⟩, k.1.1⟩ = (keptK2 r H W₀ k).old)
    (hone : ∀ ho : 1 + r.kept.idxOf k.1.1.val < r.l.length,
      arr (seatN ⟨_, ho⟩).1 (seatN ⟨_, ho⟩).2 = arr (seat k.1.1).1 (seat k.1.1).2)
    (hshown : ShownAt G r.cs r.lo seat y k.1.1) :
    ∃ xo, KeptFacts G seat seatN p orc arr seats a t fx W₀ y k (keptK2 r H W₀ k) xo := by
  obtain ⟨xo, hmsg, hsh, hn⟩ := hx_of hk hS ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩
  have hat : W₀.kept[r.kept.idxOf k.1.1.val]? = some (keptK2 r H W₀ k) :=
    hmem_of hk ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩
  obtain ⟨-, -, -, hi, -, -⟩ := entry_shape fx W₀ P12.frameIs P12.codes _ _ hat xo hmsg _ hsh
  exact ⟨xo, keptFacts_of G seat seatN p orc arr seats a t fx W₀ y P12.frameIs hchk P12.codes hG Ft
    (numAt_inj r) (hmem_of hk) (hrb_of hk hb) k xo hmsg hsh hn
    (shape_of hs ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩).1
    ((shape_of hs ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩).2.elim (fun h3 => Or.inl (Or.inr h3))
      fun h1 => Or.inr ⟨H.h0 ⟨k.1.1, k.2.fst⟩ k.2.snd, h1⟩)
    (hT_of_next fx hchk _ hi P12.next) hst hseat hlist hnum hone hshown⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptFacts_at
