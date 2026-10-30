-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/GoodFoldAt.lean: the laws of "LIN zeta" and of "SPLIT" in the form of the rule
of composition (Johnson/Desc/K14/Law/GoodFold.lean), GENERAL IN THE TWO PROMISES: on in front, on'
behind, are letters. The laws of GoodFold.lean have for their promises histories (On7, On8, On9:
"there are records and rounds that have led here"); a table whose promises are facts on a state
cannot give a history. What the two proofs spend of the promise in front is little, and is named
here.

  zeta_core       "LIN zeta", THE CORE: at any record T that holds the chain's own (get : T → St),
                  at any type of claims, at any promises with "on a, a yes: on' b", at two letters
                  for the pin (PinA in front, PinB behind). In front: PinA, and omega_col is
                  col_psi_lo(u) (OmegaCol). Behind: PinB, and (fold)'s equation at the point noted
                  (FoldAt). OF THE PROMISE IN FRONT THE PROOF SPENDS NOTHING: it hands it to the
                  premises. By fold_core (Johnson/Desc/K14/Law/FoldCore.lean), which names no kind.
  zeta_goodInAt   the same at the chain's own record, with Base on both sides: the core at
                  PinA, PinB := Base.
  OnSplit p a     WHAT "SPLIT" SPENDS, a fact on the state: two codes; and at every statement that
                  grows out of the record's, o_omega and o_u have their tables (Placed).
  onSplit_of_seated   it follows where the two messages are seated and the shape's conditions hold
                  at the codes: five plain facts on the statement and the small record.
  split_goodInAt  "SPLIT" at any promises with "on a: OnSplit" and "on a, a yes: on' b".
  seatedOk_of_front, onSplit_of_on8   the history in front of "SPLIT" gives OnSplit. (Kin:
                  seated_of_front, Johnson/Desc/K14/Law/Member.lean, and seated_of_run,
                  Johnson/Desc/K14/SharedOmega.lean: the same walk, without the shape's conditions.)
  zeta_goodIn_again, split_goodIn_again   THE TEST THAT NOTHING IS LOST: the two laws of
                  GoodFold.lean, to the letter, as instances.

What is not claimed. The premises of GoodFold.lean's laws stay. Under the letter on: at a yes a
witness that is pinned behind is pinned in front; two witnesses pinned by one statement have the
same words on o_omega and on o_u. BARE: the block decides as "LIN zeta" (hz) | as "SPLIT" (hb); the
extractor is the identity (hext); the written round reads as one typed draw (hread), at errors that
fit (fits) a count that is bounded FROM BELOW alone (hc). PinA, PinB, on and on' are letters: the
only members shown are the histories of GoodFold.lean, with Pin still a letter. A block that refuses
all has GoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodFold
import Johnson.Desc.K14.Law.FoldCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)
variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K)

/-- **"LIN zeta": the core.** T: a record that holds the chain's own. -/
theorem zeta_core [Fintype K] {T Cl : Type} (get : T → St) (pc : Piece C F T Cl W) (S : LinShape)
    (hz : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → linZeta (get d) rs = some (get d'))
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (PinA PinB : T × F.E.Str → W → Prop)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → PinB b w → PinA a w)
    (hdet : ∀ (a : T × F.E.Str) w w', on a → PinA a w → PinA a w' →
      AgreeOn (get a.1).loc.oOmega (rw w) (rw w') ∧ AgreeOn (get a.1).loc.oU.oracle (rw w) (rw w'))
    (c : Nat) (hc : S.kRow * Fintype.card K ^ (S.kRow - 1) ≤ c)
    (G : T × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin S.kRow → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r7, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r7] →
      ∃ z, (G a).tr τ = some (((), ()), z, ()) ∧ (drawn r7).map ρ.val = List.ofFn z) :
    pc.GoodIn on on' (fun a w => PinA a w ∧ OmegaCol ρ S (get a.1) (rw w))
      (fun b w => PinB b w ∧ FoldAt ρ S (get b.1) (rw w)) := by
  have inv : ∀ a τ b, pc.ior.red.out a τ = some b → ∃ r7,
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r7] ∧
        get b.1 = { get a.1 with loc := { (get a.1).loc with zFd := drawn r7 } } := by
    intro a τ b hout
    obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
    have k7 := hz _ _ _ _ hd
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
    rw [hr] at k7
    exact ⟨r7, hr, linZeta_inv (get a.1) (get b.1) r7 k7⟩
  exact fold_core pc S (le_two_pow_ceilLog2 _) hext on on' PinA PinB
    (fun a => ((get a.1).loc.psiSh.take S.kLo).map ρ.val) (fun a => (get a.1).loc.zFd.map ρ.val)
    (fun a w => omegaOf (get a.1).loc (linLayOmega (get a.1).st.codes S) (rw w))
    (fun a w => uOf (get a.1).loc (rw w)) hon hback
    (fun a w w' ha h h' => ⟨funext fun _ => (hdet a w w' ha h h').1 _,
      funext fun _ => (hdet a w w' ha h h').2 _⟩)
    (fun a τ b w _ hout => by
      obtain ⟨r7, _, e7⟩ := inv a τ b hout
      refine ⟨by simp only [e7], ?_, ?_⟩
      · funext j
        simp only [omegaOf, e7]
      · funext k
        simp only [uOf, e7])
    c hc G fits
    (fun a τ b _ hout => by
      obtain ⟨r7, hr, e7⟩ := inv a τ b hout
      obtain ⟨z, htr, hzs⟩ := hread a τ b r7 hout hr
      exact ⟨z, htr, by simp only [e7]; exact hzs⟩)

variable (Pin : St × F.E.Str → W → Prop)

/-- **"LIN zeta", general in the two promises**, at the chain's own record, with Base. -/
theorem zeta_goodInAt [Fintype K] (pc : Piece C F St Unit W) (p : Par)
    (hz : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → linZeta d rs = some d')
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : St × F.E.Str → Prop)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hdet : ∀ (a : St × F.E.Str) w w', on a → Pin a w → Pin a w' →
      AgreeOn a.1.loc.oOmega (rw w) (rw w') ∧ AgreeOn a.1.loc.oU.oracle (rw w) (rw w'))
    (c : Nat) (hc : p.S.kRow * Fintype.card K ^ (p.S.kRow - 1) ≤ c)
    (G : St × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin p.S.kRow → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r7, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r7] →
      ∃ z, (G a).tr τ = some (((), ()), z, ()) ∧ (drawn r7).map ρ.val = List.ofFn z) :
    pc.GoodIn on on'
      (fun a w => Base ρ rw Pin a w ∧ OmegaCol ρ p.S a.1 (rw w))
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) := by
  refine zeta_core ρ rw (fun d : St => d) pc p.S hz hext on on' (Base ρ rw Pin) (Base ρ rw Pin) hon
    (fun a τ b w ha hout hw => ?_) (fun a w w' ha h h' => hdet a w w' ha h.1 h'.1) c hc G fits hread
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  have k7 := hz _ _ _ _ hd
  obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
  rw [hr] at k7
  have e7 := linZeta_inv a.1 b.1 r7 k7
  have o7 : Onward a.1 b.1 := Onward.of_st (by rw [e7])
  obtain ⟨hpin, hU, hO⟩ := hw
  refine ⟨hback a τ b w ha hout hpin, ?_, ?_⟩
  · have : b.1.loc.gU = a.1.loc.gU := by rw [e7]
    rw [← this]; exact hU.back ρ o7
  · have : b.1.loc.gOmega = a.1.loc.gOmega := by rw [e7]
    rw [← this]; exact hO.back ρ o7

/-- **What "SPLIT" spends of the promise in front**: a fact on the state. -/
def OnSplit (p : Par) (a : St × F.E.Str) : Prop :=
  p.S.sharedSplitNeeded = true ∧
    ∀ T, Grows a.1.st T → Placed T p.S a.1.loc (linLayOmega a.1.st.codes p.S)

/-- It follows where the two messages are seated and the shape's conditions hold at the codes. -/
theorem onSplit_of_seated (p : Par) (a : St × F.E.Str) (hS : p.S.sharedSplitNeeded = true)
    (codes : Codes) (hs : Seated a.1.st codes p.S a.1.loc) (hok : linOk codes p.S = true) :
    OnSplit p a :=
  ⟨hS, fun T g => by rw [hs.sameCodes]; exact placed_of_seated (hs.grows g) hok⟩

/-- **"SPLIT", general in the two promises.** -/
theorem split_goodInAt (pc : Piece C F St Unit W) (p : Par) (hb : DecidesBySplit p pc.b)
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : St × F.E.Str → Prop)
    (hst : ∀ a, on a → OnSplit p a)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w) :
    pc.GoodIn on on'
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) (Base ρ rw Pin) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  obtain ⟨hS, hP⟩ := hst a ha
  have k8 := hb _ _ _ _ hd
  obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k8
  rw [hr] at k8
  obtain ⟨o8, l8⟩ := onward_split p a.1 b.1 r8 hS k8
  refine ⟨hon a τ b ha hout, fun w hw => ?_⟩
  obtain ⟨hpin, hU, hO⟩ := hw
  rw [hext]
  refine ⟨⟨hback a τ b w ha hout hpin, ?_, ?_⟩, ?_⟩
  · rw [← l8]; exact hU.back ρ o8
  · rw [← l8]; exact hO.back ρ o8
  · obtain ⟨eU, rU, sU⟩ := hU
    obtain ⟨eO, rO, sO⟩ := hO
    exact foldSaysAt ρ p a.1 b.1 eU eO r8 (rw w) hS k8 (by rw [← l8]; exact rO)
      (by rw [← l8]; exact rU) (by rw [← l8]; exact sO) (by rw [← l8]; exact sU)
      (hP b.1.st o8.grows)

/-! ## The histories are instances -/

/-- In front of "LIN zeta" the two messages are seated, at codes at which the shape's conditions
hold. -/
theorem seatedOk_of_front {p : Par} {d0 d2 d3 d6 : St} {r4 : Fmt.RoundView}
    {cols : List (Nat × List UInt64)} (h : SharedFront p d0 d2 d3 d6 r4 cols) :
    ∃ codes, Seated d6.st codes p.S d6.loc ∧ linOk codes p.S = true := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, d5, rs1, rs3, rs6, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6⟩ := h
  have hok0 := linPoint_ok p d0 d1 rs1 h1
  have hok : linOk d1.st.codes p.S = true := by rw [(linPoint_grows p d0 d1 rs1 h1).1]; exact hok0
  obtain ⟨oU1, lU1⟩ := onward_recvP ftU d1 a1 sentU idsU rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv p a2 d2 idsU h2
  obtain ⟨o3, l3⟩ := onward_laysRec p d2 d3 rs3 h3
  obtain ⟨o4, l4⟩ := onward_loc p d3 d4 r4 cols h4
  obtain ⟨oO1, lO1⟩ := onward_recvP ftO d4 b1 (withOmega p.S) idsO rO
  obtain ⟨s5, oo, sp, hoo, l5⟩ := behindOmega_inv p b2 d5 idsO h5
  obtain ⟨o6, l6⟩ := onward_joins p d5 d6 rs6 h6
  have A : Onward a1 d4 := ((cU.trans (Onward.of_st s2)).trans o3).trans o4
  have B : Onward b1 d6 := (cO.trans (Onward.of_st s5)).trans o6
  have l : d6.loc = { d2.loc with oOmega := oo, oSp := sp } := by
    rw [l6, l5, cOl, lO1, l4, l3]
  have hoU : d6.loc.oU = d2.loc.oU := by rw [l]
  have hcA : a2.st.codes = d1.st.codes := (oU1.trans cU).grows.1
  obtain ⟨nU, sU0, shU⟩ := withU_first p.S sentU hU
  obtain ⟨nO, sO0, shO⟩ := withOmega_first p.S
  exact ⟨d1.st.codes, seated_behind d1.st.codes p.S d6.loc d6.st d1 a1 d4 b1 ftU ftO sentU
    (withOmega p.S) idsU idsO nU nO rfl rU sU0 shU (by rw [hoU, l2]; exact ho) A.grows rO sO0 shO
    (by rw [l]; exact hoo) B.grows (by rw [hoU, l2, ← hcA]), hok⟩

/-- The history in front of "SPLIT" gives what "SPLIT" spends. -/
theorem onSplit_of_on8 (p : Par) (a : St × F.E.Str) (h : On8 p a) : OnSplit p a := by
  obtain ⟨d0, d2, d3, d6, r4, cols, r7, hF, h7⟩ := h
  obtain ⟨codes, hs, hok⟩ := seatedOk_of_front hF
  have e7 := linZeta_inv d6 a.1 r7 h7
  refine onSplit_of_seated p a hF.twoCodes codes ?_ hok
  rw [e7]
  exact ⟨hs.sameCodes, hs.two, hs.omega, hs.u, hs.lay⟩

/-- **Nothing is lost: "LIN zeta" as GoodFold.lean has it**, to the letter, as an instance. -/
theorem zeta_goodIn_again [Fintype K] (pc : Piece C F St Unit W) (p : Par)
    (hz : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → linZeta d rs = some d')
    (hext : ∀ a τ w, pc.ext a τ w = w)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On7 p a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On7 p a → Prm a → pc.ior.red.out a τ = some b → Prm' b)
    (hdet : ∀ (a : St × F.E.Str) w w', On7 p a → Prm a → Pin a w → Pin a w' →
      AgreeOn a.1.loc.oOmega (rw w) (rw w') ∧ AgreeOn a.1.loc.oU.oracle (rw w) (rw w'))
    (c : Nat) (hc : p.S.kRow * Fintype.card K ^ (p.S.kRow - 1) ≤ c)
    (G : St × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin p.S.kRow → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r7, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r7] →
      ∃ z, (G a).tr τ = some (((), ()), z, ()) ∧ (drawn r7).map ρ.val = List.ofFn z) :
    pc.GoodIn (fun a => On7 p a ∧ Prm a) (fun b => On8 p b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ OmegaCol ρ p.S a.1 (rw w))
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) := by
  refine zeta_goodInAt ρ rw Pin pc p hz hext (fun a => On7 p a ∧ Prm a)
    (fun b => On8 p b ∧ Prm' b) (fun a τ b ha hout => ?_)
    (fun a τ b w ha => hback a τ b w ha.1 ha.2) (fun a w w' ha => hdet a w w' ha.1 ha.2) c hc G
    fits hread
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  obtain ⟨h7, hprm⟩ := ha
  obtain ⟨d0, d2, d3, r4, cols, hF⟩ := id h7
  have k7 := hz _ _ _ _ hd
  obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
  rw [hr] at k7
  exact ⟨⟨d0, d2, d3, a.1, r4, cols, r7, hF, k7⟩, hkeep a τ b h7 hprm hout⟩

/-- **Nothing is lost: "SPLIT" as GoodFold.lean has it**, to the letter, as an instance. -/
theorem split_goodIn_again (pc : Piece C F St Unit W) (p : Par) (hb : DecidesBySplit p pc.b)
    (hext : ∀ a τ w, pc.ext a τ w = w) (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On8 p a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On8 p a → Prm a → pc.ior.red.out a τ = some b → Prm' b) :
    pc.GoodIn (fun a => On8 p a ∧ Prm a) (fun b => On9 p b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) (Base ρ rw Pin) := by
  refine split_goodInAt ρ rw Pin pc p hb hext (fun a => On8 p a ∧ Prm a)
    (fun b => On9 p b ∧ Prm' b) (fun a ha => onSplit_of_on8 p a ha.1) (fun a τ b ha hout => ?_)
    (fun a τ b w ha => hback a τ b w ha.1 ha.2)
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  obtain ⟨h8, hprm⟩ := ha
  obtain ⟨d0, d2, d3, d6, r4, cols, r7, hF, h7⟩ := id h8
  have k8 := hb _ _ _ _ hd
  obtain ⟨r8, hr⟩ := split_one _ _ _ _ hF.twoCodes k8
  rw [hr] at k8
  exact ⟨⟨d0, d2, d3, a.1, r4, cols, hF.toRun a.1 b.1 r7 r8 h7 k8⟩, hkeep a τ b h8 hprm hout⟩

-- by Lean: the two statements are GoodFold.lean's own (proofs of one proposition are equal)
example : @zeta_goodIn_again = @zeta_goodIn := rfl
example : @split_goodIn_again = @split_goodIn := rfl

end Desc.K14.Law
