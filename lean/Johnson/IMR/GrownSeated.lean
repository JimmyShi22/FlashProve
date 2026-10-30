-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrownSeated.lean: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS
THE VERIFIER's STATE ALONE: THE JOIN's SECOND, WEAKER-TO-PAY FORM: Hands IS ASKED OF THE SEATED
SUB-PROTOCOL, WITH ALL THAT ITS SEAT SAYS IN HAND. ADDITIVE: Johnson/IMR/GrownJoin.lean's
Shares AND s1_of_shares STAND; WHOEVER HAS Shares HAS THIS FORM (seated_of_shares): NOBODY's TERM TURNS.
WHY (on the join, Johnson/IMR/GrownJoin.lean). The fields hear · close · back · last of Shares ask Hands of THE LOT's BARE sub-protocol. The seated one accepts less: it rejects where a mark is left behind, and, but at K7's place, where the reply in the state is not as it was. A payer at the bare one has the first in hand (Hands' own
premises) but not the second: at an E that reads the state's reply it would owe «my sub-protocol leaves the reply» itself. Here it has it for nothing.
ON WORDS: «the state» is the verifier's state: the value of type S that the fold of the IOP as written in Lean carries from sub-protocol (block) to sub-protocol.

  SharesS N E ft Z G₀ c   ∀ k b, FlatCase Z G₀ c k b → Hands N linksW placesW E ft k b: Hands at
                          each of the ten forms of Johnson/IMR/FlatCases.lean.
  s1_of_seated      in scope: SharesS → S1 N linksW E ft c.
  seated_of_shares  Shares → SharesS.
  Yes.alone         what a payer has in hand at a sub-protocol that stands ALONE at a place not of the kind K7: the lot's own step accepts, to the same state · no mark behind · the reply as it was.
  Yes.atLinkFirstPlace        the like at a link's first place: the lot's own step from s to m · no mark at m · the row's «opened» from m to s' · no mark at s' · the reply is the same at m and s'.

What is not claimed. NO SHARE IS PAID HERE. No soundness.
-/
import Johnson.IMR.GrownJoin
import Johnson.IMR.FlatCases

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open ProofFile (Cl)

/-- **The shares, at the seated sub-protocols.** -/
def SharesS (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : Chain S Cl) : Prop :=
  ∀ k b, FlatCase Z G₀ c k b → Hands N linksW placesW E ft k b

/-- What a payer has in hand where the seated sub-protocol stands alone. -/
theorem Yes.alone {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) (hk : a.kind ≠ KindName.K7) {ft : ℕ} {s s' : S}
    (hy : Yes ft b s s') : Yes ft b' s s' ∧ s'.failed = none ∧ same s s' = true := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨e1, e2, e3⟩ := (step_alone h hk ft s s' n rs cols).1 e
  exact ⟨⟨rs, cols, n, e1⟩, e2, e3⟩

/-- The like at a link's first place. -/
theorem Yes.atLinkFirstPlace {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a)
    {ft : ℕ} {s s' : S} (hy : Yes ft b s s') :
    ∃ fs f m, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ Yes ft b' s m ∧ m.failed = none ∧ f.opened m = .ok s' ∧
      s'.failed = none ∧ ProofFile.sameReply m s' = true := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨fs, f, m, h1, h2, h3, h4, h5, h6, h7⟩ := h.step e
  exact ⟨fs, f, m, h1, h2, ⟨rs, cols, n, h3⟩, h4, h5, h6, h7⟩

/-- **Whoever has Shares has the seated form.** -/
theorem seated_of_shares {N : Numbers} {E : ℕ → S → Bool} {ft : ℕ} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} {c : Chain S Cl} (Sh : Shares N E ft Z G₀ c) : SharesS N E ft Z G₀ c := by
  intro k b h
  cases h with
  | front b hr hd =>
    refine hands_same (fun s s' hy => ?_) Sh.front
    obtain ⟨rs, cols, n, e⟩ := hy
    exact (hd s _ _ s').1 ((VerifiableInference.Desc.Sound.step_ok_iff ft b s s' rs cols n).1 e).2.2.2
  | laid l hl b hr hd => exact Sh.laid l hl b hr fun s rs gs t hy => (hd s rs gs t).1 hy
  | first l hl k0 b b' hk lot hp hj => exact Sh.first l hl k0 b b' hk lot hp hj
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    exact (Sh.hear l hl i k0 b' hi hk lot hp).under (alone_underR hla)
  | batch l hl Lk p e1 hp hal => exact Sh.batch l hl Lk e1
  | behind l hl Lk b e1 hr hd => exact Sh.behind l hl Lk b e1 hr hd
  | close l hl p Q j k0 b x hp hQ hk ex hla =>
    exact (Sh.close l hl p Q j x hp hQ ex).under (alone_underR hla)
  | cleared l hl fs f b hfs hf hr hd =>
    exact Sh.cleared l hl fs f b hfs hf hr fun s rs gs t hy => (hd s rs gs t).1 hy
  | back j k0 b b' name hk lot hp hla =>
    exact (Sh.back j k0 b' hk lot hp).under (under_bare (alone_underR hla))
  | last lot hla => exact Sh.last.under (under_bare (alone_underR hla))

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE JOIN, FROM THE SEATED FORM.** -/
theorem s1_of_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {ft : ℕ} (h : SharesS N E ft Z Bs.G₀ c) : S1 N linksW E ft c := by
  apply s1_of_hands
  rw [places_scope hS hR O]
  exact fun k b hb => h k b (flat_cases hS hR O k b hb)

end

end IM

#print axioms IM.Yes.alone
#print axioms IM.Yes.atLinkFirstPlace
#print axioms IM.seated_of_shares
#print axioms IM.s1_of_seated
