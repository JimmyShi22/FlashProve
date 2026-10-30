-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Law15At.lean: ROW 1.15 OF THE KEY FILE's TABLES, THE CLAIM's HALF, ITS «law», JOINED AT THE TABLES' FILES' OWN FILLING (baseK): THE TWO ITEMS THAT THE ROW CLOSES (grows · pin 1) HOLD AT THE VERIFIER's STATE IN FRONT OF THE PROXIMITY TEST AND THE WITNESS WITH ONE TABLE LAID AS MESSAGE 1. Two definitions; three statements with proofs. IT MOVES THE WEIGHT INTO CoreFacts AND NAMED PUBLIC FACTS; IT PAYS NONE.
OBJECT. The premise «law» of back_15 (Johnson/RunOne/Law/KeyRide15.lean), at m := tbl15 a w.
USER. Whoever joins «back» at row 1.15 (gives_of_halvesH, K12Left15H.lean: its letter tbl := tbl15).
LETTERS. X N P DK: The35.lean's. decT recOf tab: the filling's. ONE READING FOR BOTH ITEMS: GK := baseK's h₁ at the plan's own numbering; the seats atSix; the reader RK := kreadFam. i₁: the member of the six that is message 1; x₁ := ⟨sixS, i₁⟩. smpK: the typed reading of a state's OOD samples (out-of-domain samples; the library's files call such a sample the record): smpSt (Johnson/Desc/Sound/SmpShared.lean) at the first chain's statement. oNo · mem · rdT: the caller's.
  CoreAt a u: what the composition over the proximity test's law concludes at a, with u the tuple's message at x₁: ONE "there is" over the state behind the seat's door in, the group, and the tuple.
  tbl15: the table that is laid: of SOME u with CoreAt a u, by choice; it does not read the witness.
  law_at_u: THE SUBSTANCE: at ANY u with CoreAt a u. pin 1: the candidate at the reading's chosen seed is a candidate at the seed that the state spells (the library's candidate sees a seed through its sample map alone), and there "a candidate can be laid" (Johnson/Top/Fire/Code/CandCanBeLaid.lean) · pin_laid. grows: grows_laid (K12Law15.lean).
  law_15: at tbl15: the choice's own property: one "there is", opened once.
  coreAt_of: CoreAt has a member wherever core_15 (K12Core15.lean) applies.
Limits. CoreFacts is a premise of coreAt_of; every premise of law_at_u is named with its meant payer in a page on row 1.15 that is not in this library. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Law15
import Johnson.RunOne.Law.K12Core15
import Johnson.Top.Fire.Code.CandBridge
import Johnson.Desc.Sound.SmpShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.Law.K12Law15At
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes.Maker
open _root_.Run
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open LPFD LPFD.CandLaid

/-- The member of the six that is message 1. -/
def i₁ : Fin six.length := ⟨1, by decide⟩

abbrev x₁ : Mem := ⟨sixS, i₁⟩

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {Cells Rec : Type}
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (tab : Cells → ℕ → ℕ → OnBytes.F)
  (oNo : Mem → ℕ) (mem : ℕ → Option Mem)
  (rdT : (x : Mem) → ((sigOf csKey x.1.l).om x.2).Msg → Part → ℕ → GE)

abbrev FR : Frame := frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0

/-- The one reading. -/
abbrev GK := (baseK (Cells := Cells) csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc).h₁

abbrev RK : KRead Cells Fill.Tab := kreadFam csKey six numSix atSix tab

abbrev smpK := smpSt csKey oNo (fun a : Xi × FirstState => a.2.d.st)

/-- **What the composition concludes at a, with u the tuple's message at x₁.** -/
def CoreAt (a : (Xi × FirstState) × (FR DK).E.Str) (u : (OmAt csKey six i₁).Msg) : Prop :=
  ∃ (t : T12) (G0 : Group) (m : (x : Mem) → ((sigOf csKey x.1.l).om x.2).Msg), m x₁ = u ∧
    enterAndAsk (enterRanges (oneAt X)) (rangesParams N) a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
    AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList (_root_.Desc.K14.Law.wordsT csKey mem rdT m) ∧
    CandAt csKey (Fk X N P) (smpK oNo) x₁ a.1 (strsOf (FR DK) a.2) (m x₁)

open Classical in
/-- **The table that is laid**: of some u with CoreAt a u. -/
def tbl15 (a : (Xi × FirstState) × (FR DK).E.Str) (_ : Wit Cells Unit Fill.Tab) : Fill.Tab :=
  if h : ∃ u, CoreAt X N P DK oNo mem rdT a u then ofU csKey (six.get i₁).1 (six.get i₁).2 h.choose else fun _ _ => 0

/-- **«law» at any u with CoreAt a u.** -/
theorem law_at_u (a : (Xi × FirstState) × (FR DK).E.Str) (w : Wit Cells Unit Fill.Tab) (u : (OmAt csKey six i₁).Msg)
    (hu : CoreAt X N P DK oNo mem rdT a u)
    (hrows : ∃ g G, (readers₁ (oneAt X)).grpB a.1.2 = some g ∧ a.1.2.d.st.groups[g]? = some G ∧ G.members.toList = [1] ∧ G.rows.size ≠ 0)
    (hdoor : ∀ t, enterAndAsk (enterRanges (oneAt X)) (rangesParams N) a.1.2 = .ok t → t.st = a.1.2.d.st ∧ (readers₁ (oneAt X)).grpB a.1.2 = some t.g)
    (hx : ∃ x, a.1.2.d.st.oracles[1]? = some x) (hI : InOrder a.1.2.d.st) (hK : OpenKinds a.1.2.d.st)
    (hseed : ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.1.2.d.st 1 ρ y) (hT : K1.Tie csKey (six.get i₁).1)
    (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (horc : (plan₁ (oneAt X)).orc 1 = some 1) (hnum : (plan₁ (oneAt X)).num 1 = some 1)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1)
    (told : ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true)
    (o : VerifiableInference.Desc.Oracle) (ho : (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp)
    (hz : (GK X decT recOf).smp a.1 (seatAt six numSix atSix i₁).1 (seatAt six numSix atSix i₁).2 = some z)
    (hsh : Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (FR DK) a.2) i₁)
    (ha : ArrOk (GK X decT recOf) atSix [1]) (hr : ReadsPinned (GK X decT recOf) atSix (RK tab) [1])
    (hi : LayIdem (GK X decT recOf)) (hsame : (RK tab).same = fun a b => OnBytes.Slice.readE a = OnBytes.Slice.readE b) :
    ∀ i ∈ [KItem.grows, KItem.pin 1], i.holds (Fk X N P) (GK X decT recOf) atSix (meaning₁At (oneAt X) (RK tab)) a.1
      (strsOf (FR DK) a.2) (layAt atSix [1] (fun _ => ofU csKey (six.get i₁).1 (six.get i₁).2 u) w) := by
  obtain ⟨t, G0, m, rfl, ht, hG0, hall, hcand⟩ := hu
  -- pin 1 first
  obtain ⟨ρ, y, hs⟩ := hseed
  obtain ⟨zz, hz1, hz2, hz3⟩ := K1.smpAt_of csKey (six.get i₁).1 (six.get i₁).2 a.1.2.d.st 1 ρ y hT hs
  obtain ⟨σ, hσ, hc⟩ := (candAt_iff csKey (Fk X N P) (smpK oNo) x₁ a.1 (strsOf (FR DK) a.2) (m x₁)).1 hcand
  have e : zz = σ := by
    have h' : K1.smpAt csKey (six.get i₁).1 (six.get i₁).2 a.1.2.d.st (oNo x₁) = some σ := hσ
    rw [hoNo, hz1] at h'
    exact Option.some.inj h'
  subst e
  have hc' : Cb.Ood.Cand
      ((OmAt csKey six i₁).InList (symsW csKey (six.get i₁).1 (six.get i₁).2
        (wordOf (Fk X N P) (strsOf (FR DK) a.2) (seatAt six numSix atSix i₁).1 (seatAt six numSix atSix i₁).2)))
      (OmAt csKey six i₁).Z.val ρ (fun _ => y) (m x₁) := by
    refine ⟨hc.1, ?_⟩
    have h2 : (portOmZ csKey (six.get i₁).1 (six.get i₁).2).Z.val zz.1 (m x₁) = zz.2 := hc.2
    rw [hz2, hz3] at h2
    exact h2
  have hS : seedIsS csKey six numSix (rowIsK csKey six) (src₁ (plan₁ (oneAt X)).orc) i₁ a.1 ρ (fun _ => y) :=
    (seedIsS_iff₁ csKey six numSix (plan₁ (oneAt X)).orc i₁ a.1 ρ _).2 ⟨1, horc, y, hs, rfl⟩
  have h3 := cand_laid₁ (Fk X N P) (strsOf (FR DK)) decT recOf (plan₁ (oneAt X)).orc tab i₁ hlog told a.1 a.2 o z
    (m x₁) ρ (fun _ => y) ho hz hS hsh hc'
  -- grows
  obtain ⟨g, G, hg, hG, hone, hne⟩ := hrows
  obtain ⟨e1, e2⟩ := hdoor t ht
  have eg : t.g = g := Option.some.inj (e2.symm.trans hg)
  rw [e1, eg] at hG0 hall
  obtain rfl : G = G0 := Option.some.inj (hG.symm.trans hG0)
  obtain ⟨x, hx⟩ := hx
  intro i hi'
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact K12Law15.grows_laid csKey (plan₁ (oneAt X)) (RK tab) (readers₁ (oneAt X)) _ _ _ _ (GK X decT recOf) atSix a.1
      (strsOf (FR DK) a.2) w g G 1 x hg hG horc hx hne hone hsame hI hK mem rdT hrd m x₁ hmem hnum hall ha hr hi
      (fun part k => h3.2.2 part k)
  · obtain rfl := List.mem_singleton.1 hi'
    exact K12Law15.pin_laid (Fk X N P) (GK X decT recOf) atSix 1 _ a.1 (strsOf (FR DK) a.2) w ha hi o z ho hz h3.1

/-- **«law» at the table that is laid.** One "there is", opened once. -/
theorem law_15 (a : (Xi × FirstState) × (FR DK).E.Str) (w : Wit Cells Unit Fill.Tab)
    (h : ∃ u, CoreAt X N P DK oNo mem rdT a u)
    (hrows : ∃ g G, (readers₁ (oneAt X)).grpB a.1.2 = some g ∧ a.1.2.d.st.groups[g]? = some G ∧ G.members.toList = [1] ∧ G.rows.size ≠ 0)
    (hdoor : ∀ t, enterAndAsk (enterRanges (oneAt X)) (rangesParams N) a.1.2 = .ok t → t.st = a.1.2.d.st ∧ (readers₁ (oneAt X)).grpB a.1.2 = some t.g)
    (hx : ∃ x, a.1.2.d.st.oracles[1]? = some x) (hI : InOrder a.1.2.d.st) (hK : OpenKinds a.1.2.d.st)
    (hseed : ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.1.2.d.st 1 ρ y) (hT : K1.Tie csKey (six.get i₁).1)
    (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (horc : (plan₁ (oneAt X)).orc 1 = some 1) (hnum : (plan₁ (oneAt X)).num 1 = some 1)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1)
    (told : ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true)
    (o : VerifiableInference.Desc.Oracle) (ho : (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp)
    (hz : (GK X decT recOf).smp a.1 (seatAt six numSix atSix i₁).1 (seatAt six numSix atSix i₁).2 = some z)
    (hsh : Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (FR DK) a.2) i₁)
    (ha : ArrOk (GK X decT recOf) atSix [1]) (hr : ReadsPinned (GK X decT recOf) atSix (RK tab) [1])
    (hi : LayIdem (GK X decT recOf)) (hsame : (RK tab).same = fun a b => OnBytes.Slice.readE a = OnBytes.Slice.readE b) :
    ∀ i ∈ [KItem.grows, KItem.pin 1], i.holds (Fk X N P) (GK X decT recOf) atSix (meaning₁At (oneAt X) (RK tab)) a.1
      (strsOf (FR DK) a.2) (layAt atSix [1] (fun _ => tbl15 X N P DK oNo mem rdT a w) w) := by
  classical
  have e : tbl15 X N P DK oNo mem rdT a w = ofU csKey (six.get i₁).1 (six.get i₁).2 h.choose := by
    unfold tbl15
    exact dif_pos h
  rw [e]
  exact law_at_u X N P DK decT recOf tab oNo mem rdT a w h.choose h.choose_spec hrows hdoor hx hI hK hseed hT hoNo hmem hrd horc hnum hlog told o ho z hz hsh ha hr hi hsame

/-- **CoreAt has a member wherever the composition applies.** -/
theorem coreAt_of (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12)
    (ht : enterAndAsk (enterRanges (oneAt X)) (rangesParams N) a.1.2 = .ok t)
    (facts : CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) (nuOf (rangesParams N) nl t) rad (smpK oNo) mem (· = x₁) t a.2 a.1
      (strsOf (FR DK) a.2))
    (hI : InOrder t.st)
    (hq : QN (rangesParams N) (NTuple (FR DK) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) :
    ∃ u, CoreAt X N P DK oNo mem rdT a u := by
  obtain ⟨G0, hG, m, hall, hc⟩ := K12Core15.core_15 X N P DK csKey (smpK oNo) mem (· = x₁) rdT hrd nl rad rd a t facts hI hq
  exact ⟨m x₁, t, G0, m, rfl, ht, hG, hall, hc x₁ rfl⟩

end

end Johnson.RunOne.Law.K12Law15At

#print axioms Johnson.RunOne.Law.K12Law15At.law_at_u
#print axioms Johnson.RunOne.Law.K12Law15At.law_15
#print axioms Johnson.RunOne.Law.K12Law15At.coreAt_of
