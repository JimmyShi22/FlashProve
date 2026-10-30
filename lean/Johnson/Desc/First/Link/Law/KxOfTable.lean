-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KxOfTable.lean: `kxAll` (SortLetters.lean) OF WHAT IS FIXED, AT ALL 25
LINKS, FROM "REACHED" AND THE TABLE's PROMISE IN FRONT OF THE BATCHING. A test with code, two lines
by the kernel, and theorems: joins of other files' lemmas.
Why. KxAtFront.lean has the digits' half of `kxAll`, and the calls' half from `K3LeftOn` at the
calls' seat. That is what the table's item leftOn says, and the batching's row asks that item in
front. Here it is drawn from the promise.
  `pubP_of_onT`: the promise without a mark says `Mg.pubP q` of every public item q that is open at
    the border: its last clause (`onAt`, Johnson/Desc/First/Borders.lean). `leftAsked k l`: the item
    leftOn l is among the public items open at number k l of the full list. `leftAsked_full`: **yes
    in front of all 25 batchings: by the kernel.** `leftAsked_off`: **the negative line: one number
    further, at none:** the batching's row drops the item.
  `leftOn_at_front`: so the promise in front of link l's batching gives `k3LeftOnItemAt X l`
    (Johnson/Desc/First/Look/K3LeftItem.lean): at the composed filling `pubP (.leftOn l)` is that
    sentence by definition. `kxCalls_of_item`, `kxCalls_of_table`: **the calls' half of `kxAll`, at
    lmC := p.lm, jC := p.first, p the calls' place's own parameters.**
  `kx_of_table`: **`kxAll pC.lm pC.first lm pD.first (fixed9 (phiAll u psiAll) a.1)` at a.1 reached
    at `frontAt l`, l < 25, under the promise there.**
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; the promise.
Limits. TWO LETTERS STAND FOR THE PUBLIC PARAMETERS: X (the filling's) at the calls' place,
`Bs.G₀.W` (the blank letters') at the digits': that they are one is not shown here. hp is shown of
nothing here. The letter lm is free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.KxAtFront
import Johnson.Desc.First.Link.Law.FourOfTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers flatPlacesOf pubSets)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (K3Ok K3LeftOn k3LeftOnItemAt ok_of_shapeOf shape_some)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The promise says `pubP` of every public item that is open at the border.** -/
theorem pubP_of_onT {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (pl : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onT N Mg links pl get k a) (q : Pub)
    (hq : q ∈ (pubSets Mg.more links pl)[k]?.getD []) : Mg.pubP q (get a.1) := by
  obtain ⟨h1, h2⟩ := h
  unfold onQ First.onAt at h1
  obtain ⟨-, hm | ⟨-, -, -, hp⟩⟩ := h1
  · exact absurd hm h2
  · exact hp q hq

/-- The item leftOn l is among the public items open at number k l of the full list. -/
def leftAsked (k : ℕ → ℕ) (l : ℕ) : Bool :=
  ((pubSets moreAll fullList (flatPlacesOf fullList true))[k l]?.getD []).contains (.leftOn l)

set_option maxRecDepth 1000000 in
/-- **(W) In front of all 25 batchings.** -/
theorem leftAsked_full : (List.range 25).all (leftAsked frontAt) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** One number further: at no link. -/
theorem leftAsked_off : (List.range 25).any (leftAsked fun l => frontAt l + 1) = false := by
  decide +kernel

/-- **THE CALLS' HALF OF `kxAll`, FROM WHAT THE ITEM SAYS.** -/
theorem kxCalls_of_item (u : HTailF2) {X : Verify.Public} {m : ℕ} {s : S}
    (h : k3LeftOnItemAt X m s) :
    ∀ p, placeAt X m false = some p → K3Ok hdCalls p.lm p.first (fixed9 (phiAll u psiAll) s) := by
  intro p₀ hp₀
  obtain ⟨p, e, ⟨hh, e1, L⟩, -⟩ := h
  obtain rfl : p = p₀ := Option.some.inj (e.symm.trans hp₀)
  exact k3Ok_of_leftOn (phiAll u psiAll) hdCalls S.lookHeard? (hdCalls_all u) L
    (ok_of_shapeOf (shape_some p hh e1))

variable {Fr : Frame} {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **THE PROMISE IN FRONT OF A BATCHING GIVES WHAT THE ITEM leftOn SAYS.** -/
theorem leftOn_at_front (Nm : Numbers) (z : P) {l : ℕ} (hl : l < 25) (a : S × Fr.E.Str)
    (ha : onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s : S => (z, s))
      (frontAt l) a) : k3LeftOnItemAt X l a.1 := by
  have h := List.all_eq_true.1 leftAsked_full l (List.mem_range.2 hl)
  have hq : Pub.leftOn l ∈ (pubSets (mgAll 𝔇 mgBase).more fullList
      (flatPlacesOf fullList true))[frontAt l]?.getD [] := by
    rw [mgAll_more_base 𝔇]
    exact List.contains_iff_mem.1 h
  exact pubP_of_onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true)
    (fun s : S => (z, s)) (frontAt l) a ha (.leftOn l) hq

/-- **THE CALLS' HALF OF `kxAll`, FROM THE PROMISE.** -/
theorem kxCalls_of_table (Nm : Numbers) (z : P) {l : ℕ} (hl : l < 25) (a : S × Fr.E.Str)
    (ha : onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s : S => (z, s))
      (frontAt l) a) (u : HTailF2) :
    ∀ p, placeAt X l false = some p →
      K3Ok hdCalls p.lm p.first (fixed9 (phiAll u psiAll) a.1) :=
  kxCalls_of_item u (leftOn_at_front 𝔇 Nm z hl a ha)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Fd : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **`kxAll` FROM «REACHED» AND THE TABLE's PROMISE, AT ALL 25 LINKS.** -/
theorem kx_of_table (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL Fd Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {q : Q} (a : S × Fr.E.Str)
    (h : Reach 0 c.blocksInOrder start (frontAt l) (q, a.1)) (Nm : Numbers) (z : P)
    (ha : onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s : S => (z, s))
      (frontAt l) a) (lm : ℕ) (u : HTailF2) :
    ∀ pC pD, placeAt X l false = some pC → placeAt Bs.G₀.W l true = some pD →
      kxAll pC.lm pC.first lm pD.first (fixed9 (phiAll u psiAll) a.1) := by
  intro pC pD hC hD
  have hB := ledger_at_front 𝔇 Nm z hl a ha
  refine ⟨kxCalls_of_table 𝔇 Nm z hl a ha u pC hC, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    exact kxDigits_head hS hR O hp (z := q) (c' := a.1) h hB lm u pD hD
  · have e : frontAt l = 14 * l + 9 := by
      unfold frontAt
      rw [if_neg h24]
    rw [e] at h
    exact kxDigits_front hS hR O hp (by omega : l < 24) h hB lm u pD hD

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pubP_of_onT
#print axioms VerifiableInference.Desc.LinkJoin.leftAsked_full
#print axioms VerifiableInference.Desc.LinkJoin.leftAsked_off
#print axioms VerifiableInference.Desc.LinkJoin.kxCalls_of_item
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_at_front
#print axioms VerifiableInference.Desc.LinkJoin.kxCalls_of_table
#print axioms VerifiableInference.Desc.LinkJoin.kx_of_table
