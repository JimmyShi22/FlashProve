-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyAt15Nums.lean: THEOREMS. **Four more premises of the law at the key file's proximity test on its first chain (row 1.15; field r1_15), in their users' own letters, from the equations that hold in the goals' scope.**
WORDS. Key.descriptionFromSource X N P: the key file's IOP as written in Lean; a block: a sub-protocol; the verifier's state: what it carries between two sub-protocols; seed · tt below: a sent message's own out-of-domain (OOD) seed and answer, in the program's words.
TWO NOTIONS OF «TWO LOOKUPS» ARE ABOUT: (Key.lookupsOf one).length = 2 (the verifier program's list, made of the ranges and the matrix: two_lookups, Johnson/RunOne/KeyAt15Base.lean) and one.ranges.lookups.length = 2 (the public parameters' own list: hn_scope, here). In scope both are closed facts; no law here ties them outside it.
OBJECT AND USERS: hn · hR · hans of hmask_15 (Johnson/RunOne/Law/Hmask15.lean) and of back_15_at (Johnson/RunOne/Law/K12Back15.lean): HELD BY A REAL CALL: hmask_15_scope. hm of the core facts at 1.15: MATCHED BY READING ALONE. (Where this and lean/THEOREM.md differ, the page holds.)
  hn_scope | hans_scope        the public parameters list two lookups · the lookups' own message counts an answer
  room_full | room_no | hR_scope   by the kernel: what all lookups take fits the two messages' mask rows; a negative test (an index shape without a mask row); then in scope
  sampleL_of_reads             at letters: from «sampled, and its one sample row is Send.form's at a seed that reads as ρ, every coordinate canonical» and five public conditions on the shape: the test sampleL (Johnson/Desc/K12/Law/SampleOk.lean) says yes at every member with that shape and the number 1 (by sampleL_of_seedA, Johnson/Desc/K12/Law/SampleOfSeed.lean)
  five_mul                     by the kernel: the five conditions at csKey · shMul
  hm_15_scope                  **at every state reached behind fifteen sub-protocols: message 1 stands, has the shape shMul, and sampleL says yes**
  nums15_at                    seven_at's seven premises ⊢ the four
  hmask_15_scope               **the fit, as a call**: hmask_15 with hR · hans · hn paid
What is not claimed. That scope's premises hold at any files. The users' other premises. Nothing on soundness.

-/
import Johnson.RunOne.KeyAt15Base
import Johnson.RunOne.KeySeedOk
import Johnson.RunOne.Law.Hmask15
import Johnson.Desc.K12.Law.SampleOfSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K3.KeyLaw (RoomFor)
open VerifiableInference.Desc.Ground (ok)
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open Johnson.Pack (bitsZ)
open Johnson.Top.H (csKey shIdx shMul)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁)
open H2K.Pin (sampleL sampleL_of_seedA mainB maskB)
open H2K.First (Seat1)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)

theorem hn_full : keyFull.ranges.x.lookups.length = 2 := by decide +kernel

theorem hn_scope (X : Key.Source) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) : X.Y.k.oneTime.ranges.lookups.length = 2 := by
  rw [hr]; exact hn_full

theorem hans_scope (X : Key.Source) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0 := by
  rw [hr, msg_shape_full']; decide

theorem room_full : RoomFor keyFull.ranges.x (Wf.matrixOf keyFull.once.shape) keyFull.codes keyFull.once.input.shape := by decide +kernel
/-- A negative test: at an index shape without a mask row there is no room. -/
theorem room_no : ¬ RoomFor keyFull.ranges.x (Wf.matrixOf keyFull.once.shape) keyFull.codes { keyFull.once.input.shape with maskRows := 0 } := by decide +kernel

theorem hR_scope (X : Key.Source) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (hl : X.Y.k.oneTime.lin = keyFull.once.shape)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) :
    RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape := by
  rw [hr, hl, hc, hi]; exact room_full

/-- At letters: the test sampleL (K12/Law/SampleOk.lean) on a member's sample says yes. -/
theorem sampleL_of_reads (K : Codes) (sh : OracleShape) (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : Row) (tt : E)
    (ρ : (Fin (bitsZ K sh) → GE) × GEˣ) (hs : x.sampled = true) (hform : Send.form K sh 1 seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }]) (hread : K1.ReadsOne K sh seed.z seed.beta ρ)
    (hall : ∀ c ∈ seed.z, okE c = true) (h1 : sh.answers = 1) (hsome : 0 < sh.mainRows ∨ 0 < sh.maskRows)
    (hcase : (0 < sh.maskRows ∨ sh.mainDeg = 3) ∨ (sh.maskRows = 0 ∧ sh.mainDeg = 1))
    (hpM : sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K sh).ell = (mainB K sh).ell)
    (hpZ : sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K sh).ell = (maskB K sh).ell) :
    ∀ m : Seat1, m.sh = sh → m.id = 1 → ok (sampleL K m x) = true := by
  intro m hsh hid
  subst hsh
  exact sampleL_of_seedA K m x seed row0 tt ρ.2 hs (by rw [hid]; exact hform) hrows hread.long hread.factor.symm hall h1 hsome hcase hpM hpZ

/-- By the kernel: the five public conditions at the written codes and the shape shMul. -/
theorem five_mul : shMul.answers = 1 ∧ (0 < shMul.mainRows ∨ 0 < shMul.maskRows) ∧
    ((0 < shMul.maskRows ∨ shMul.mainDeg = 3) ∨ (shMul.maskRows = 0 ∧ shMul.mainDeg = 1)) ∧
    (shMul.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB csKey shMul).ell = (mainB csKey shMul).ell) ∧
    (shMul.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB csKey shMul).ell = (maskB csKey shMul).ell) := by decide +kernel

/-- **hm at every state reached behind fifteen sub-protocols.** -/
theorem hm_15_scope (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D' : WholeD) :
    ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D' 15 a → ∃ o, a.2.d.st.oracles[1]? = some o ∧ o.shape = shMul ∧
      ∀ m : Seat1, m.sh = shMul → m.id = 1 → ok (sampleL csKey m o) = true := by
  intro a h
  have hK : X.Y.k.oneTime.codes = csKey := hc.trans codes_full
  have hS : X.Y.k.oneTime.ranges.message.shape = shMul := by rw [hr]; exact msg_shape_full'
  obtain ⟨ρ, y, -, o, seed, row0, tt, ho, hsh, hsm, hform, hrows, hread, -, -, hall⟩ :=
    Johnson.RunOne.KeyMsg.member_one_ok_scope hp hc hr D' 13 a h
  refine ⟨o, ho, hsh.trans hS, ?_⟩
  have key := sampleL_of_reads X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape o seed row0 tt ρ hsm hform hrows hread hall
    (by rw [hS]; exact five_mul.1) (by rw [hS]; exact five_mul.2.1) (by rw [hS]; exact five_mul.2.2.1)
    (by rw [hS, hK]; exact five_mul.2.2.2.1) (by rw [hS, hK]; exact five_mul.2.2.2.2)
  intro m hm1 hm2
  rw [← hK]
  exact key m (hm1.trans hS.symm) hm2

/-- **The four, in scope.** -/
theorem nums15_at {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true) :
    X.Y.k.oneTime.ranges.lookups.length = 2 ∧
    RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape ∧
    X.Y.k.oneTime.ranges.message.shape.answers ≠ 0 ∧
    (∀ (D' : WholeD) (a : Xi × FirstState), Hist₁ (Fk X N P) D' 15 a → ∃ o, a.2.d.st.oracles[1]? = some o ∧ o.shape = shMul ∧
      ∀ m : Seat1, m.sh = shMul → m.id = 1 → ok (sampleL csKey m o) = true) := by
  obtain ⟨-, hr, hl, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact ⟨hn_scope X hr, hR_scope X hr hl hc hi, hans_scope X hr, fun D' => hm_15_scope X N P hp hc hr D'⟩

/-- **The fit, as a call**: hmask_15 with its three public premises paid in scope's equations. -/
theorem hmask_15_scope {Cells M Smp Rec : Type} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (hl : X.Y.k.oneTime.lin = keyFull.once.shape)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input)
    (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str) (hp : (Johnson.RunOne.Sound.FK X N P).planOk = true) (a : Xi × FirstState)
    (h : Hist₁ (Key.descriptionFromSource X N P) D 15 a) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where) (R : KRead Cells M)
    (w : Wit Cells Unit M) (m : M) (ha : ArrOk G at_ [0]) (hrd : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0]) :
    ∀ l ks, l < 2 → (readers₁ X.Y.k.oneTime).keysAt a.2 l = some ks → ∀ x ∈ ks,
      Model.Reading.gl.val (formAt (mkOf (plan₁ X.Y.k.oneTime) R (layAt at_ [1] (fun _ => m) w)) x.masks) =
        Model.Reading.gl.val (formAt (mkOf (plan₁ X.Y.k.oneTime) R w) x.masks) :=
  Johnson.RunOne.Law.Hmask15.hmask_15 D y hp (hR_scope X hr hl hc hi) (hans_scope X hr) (hn_scope X hr) a h G at_ R w m ha hrd hs

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.hn_scope
#print axioms Johnson.RunOne.KeyLetters.hans_scope
#print axioms Johnson.RunOne.KeyLetters.room_full
#print axioms Johnson.RunOne.KeyLetters.room_no
#print axioms Johnson.RunOne.KeyLetters.hR_scope
#print axioms Johnson.RunOne.KeyLetters.sampleL_of_reads
#print axioms Johnson.RunOne.KeyLetters.five_mul
#print axioms Johnson.RunOne.KeyLetters.hm_15_scope
#print axioms Johnson.RunOne.KeyLetters.nums15_at
#print axioms Johnson.RunOne.KeyLetters.hmask_15_scope
