-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Members32.lean: The key file's
tables, row 3.2 (the proximity test on the last chain's own group): «left» OF `law_32_coreM₂` |
`back_32_LM₂` (K12Law32Core.lean · K12Back32.lean), MEMBER BY MEMBER, at the reading smpSt csKey
oNo (·.2.st). The like of `left_29` | `back_29S` (K12Members29.lean) and `left_210`
(K12Members210.lean). A definition, statements and proofs; each proof is book-keeping and calls.
WHAT PARTS THIS ROW: THREE MEMBERS, in the group's order: I (the index masks; number oI; the six's 0: mask
rows alone) · V (number loc.w; the six's 2: ROWS OF BOTH KINDS) · Omega (number loc.w + 2; the six's 4:
main rows alone). At V the guarded conjunct of the remainder opens: so the PARTED remainder `MemberLeft₂`
(Johnson/Desc/K12/Coin/MemberAtYes.lean) is what is shown.
  `memberLeft₂_of_seed`: GENERAL: `MemberLeft₂` from the sendings' invariant K1.SeedIs, no acceptance spent:
    `memberLeft_of_seed` (Coin/MemberOfSeed.lean) with, in the place of «rows of one kind», the remainder's
    own new conjunct. KIN: it gives that lemma back (with `MemberLeft.parted`)
    at Or.inl.
  `shapes_32`: the closed facts on the three shapes, by the kernel. KIN: `hO_six` says its
    third part.
  `left_32`: the premise «left», sign for sign, from: the codes · the group's members · K1.SeedIs at the
    three · oNo | mem at the three · I's tree's depth · «V's OOD seed's point is canonical» · the fit at the
    three · the word at the three.
  `back_32_LS` := `back_32_LM₂` … (`left_32` …) …: that the two fit is hereby held by Lean.
  BESIDE THEM: WHAT FALLS TO K1.SeedIs: `cod_of_seed` · `sampled_of_seed` (its own text) ·
  `sm_of_seed₃_lo` | `sm_of_seed₃_own` (the OOD seeds' tie of the tables' files' bridge at the reading
  smpSt: one fact with the seeds) · `word_at_32`: hwI | hwV | hwO's form, general in the member, from
  `word_32S`.
  ALSO HERE: `seedOk_of_part` | `_begun` | `_made` | `_fixes` (SeedOk, KeySeedOk.lean, carried to the plain
  data's statement: SeedAtKind.lean's four lemmas on K1.SeedIs, retyped for SeedOk by program) · `okV_of_seedOk`:
  hokV's body from SeedOk at the state behind the door in, by `seedOk_reads` · `dep_at_32`: a
  member's tree's depth is its code's.
What it is not. NO EXAMPLE. EVERY PREMISE OF left_32 IS A DEBT: lies | owed: hcod · hsdI | hsdV | hsdO:
at_32′ (SeedAt32.lean: off the history, under hfit; at V it hands SeedOk) · hgm: out of the border's promise
(`shape32_facts` · `grpIs_facts`, K12Law32Core.lean) · hokV: seedOk_reads, carried to the plain
data's statement: the carriage is K12's files', not typed · hdep · hfI | hfV | hfO: K12's files', not typed ·
hwI | hwV | hwO: `word_32S` (K12Left32.lean) by one rewriting, under its own premises. It pays no field of the
tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12Back32
import Johnson.Desc.K12.Coin.MemberOfSeed
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.Sound.SeamGroup
import Johnson.Desc.Sound.SmpShared
import Johnson.RunOne.KeyFillSeedAt
import Johnson.RunOne.KeyFillChains
import Johnson.RunOne.KeySeedOk
import Johnson.RunOne.Law.K12Left32

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Members32
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf smpSt Piece held Sending Mem)
open _root_.Run (ckP)
open Cb Cb.Ood Johnson.Pack OnBytes.Maker
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (strOf layOf tabP NTuple)
open H2K.Pub (johOk sgOf)
open _root_.Desc.K14.Law.Fence (codes_fixed member_of_seedIs six_at_member)
open Johnson.RunOne.Law.K12Law32Core (i0 i2 i4)

/-- **`MemberLeft₂` from the sendings' invariant: no acceptance is spent.** General. -/
theorem memberLeft₂_of_seed (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (t : T12) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain)
    (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (x : Mem) (s : OracleShape) (e0 : ℕ)
    (hx : x.1.l.get x.2 = (s, e0)) (hT : K1.Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (yv : GE) (hseed : K1.SeedIs cs s t.st (D.mems.get j).id ρ yv)
    (hsmp : smp a0 x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id)
    (h1 : s.answers = 1)
    (hboth : ¬ (0 < s.mainRows ∧ 0 < s.maskRows) ∨
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
        D.st.oracles[(D.mems.get j).id]? = some o ∧
        Send.form cs s (D.mems.get j).id seed 0 = some row0 ∧
        o.sampleRows.toList = [{ row0 with target := tt }] ∧
        bitsZ cs s ≤ seed.z.length ∧ (β : GE) = OnBytes.Slice.readE seed.beta ∧ ∀ c ∈ seed.z, okE c = true)
    (hcase : (0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1))
    (hsite : (0 < s.mainRows ∧ (s.maskRows = 0 → cs.mask.size ≤ s.maskCode)) ∨
      (0 < s.maskRows ∧ cs.base.size ≤ s.code ∧ (D.mems.get j).tsh.logN ≤ a.Z.a))
    (h3 : rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs s))
    (h5 : mem (D.mems.get j).id = some x)
    (h7 : HEq (strOf cs s e0 (layOf (D.mems.get j))
        (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
      (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)) :
    MemberLeft₂ cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  obtain ⟨hs, _⟩ := member_of_seedIs hf default j hseed
  obtain ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩ :=
    six_at_member cs smp a0 hf default j x e0 hx hT hseed hsmp
  subst hs
  exact ⟨h1, hcase, hsite, h3, hx, h5, ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩, hboth, h7⟩

/-- **The closed facts on the three shapes.** I: mask rows alone · V: a main row · Omega: main rows
alone. -/
theorem shapes_32 :
    (¬ (0 < (six.get i0).1.mainRows ∧ 0 < (six.get i0).1.maskRows) ∧
      0 < (six.get i0).1.maskRows ∧ csKey.base.size ≤ (six.get i0).1.code) ∧
    (0 < (six.get i2).1.mainRows ∧ 0 < (six.get i2).1.maskRows) ∧
    (¬ (0 < (six.get i4).1.mainRows ∧ 0 < (six.get i4).1.maskRows) ∧
      (six.get i4).1.mainDeg = 3 ∧ 0 < (six.get i4).1.mainRows ∧
      csKey.mask.size ≤ (six.get i4).1.maskCode) := by
  decide +kernel

/-- Which of the six sits at the j-th member. -/
def ix32 {n : ℕ} (j : Fin n) : Fin six.length := if j.val = 0 then i0 else if j.val = 1 then i2 else i4

theorem ix32_0 {n : ℕ} (j : Fin n) (h : j.val = 0) : ix32 j = i0 := if_pos h
theorem ix32_1 {n : ℕ} (j : Fin n) (h : j.val = 1) : ix32 j = i2 :=
  (if_neg (by omega)).trans (if_pos h)
theorem ix32_2 {n : ℕ} (j : Fin n) (h : j.val = 2) : ix32 j = i4 :=
  (if_neg (by omega)).trans (if_neg (by omega))

/-- **«left» of `law_32_coreM₂`, member by member.** -/
theorem left_32 {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (nl : ℕ → ℕ)
    (r : Fmt.M1.Stage → ℕ) (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (x : (P₃ × St₃) × Fr₃.E.Str) (oI : ℕ)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (x.1.2.loc.w + 2) = some ⟨sixS, i4⟩)
    (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.own]? = some G0 →
      G0.members.toList = [oI, x.1.2.loc.w, x.1.2.loc.w + 2])
    (hsdI : ∃ ρ yv, K1.SeedIs csKey (six.get i0).1 x.1.2.st oI ρ yv)
    (hsdV : ∃ ρ yv, K1.SeedIs csKey (six.get i2).1 x.1.2.st x.1.2.loc.w ρ yv)
    (hsdO : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 x.1.2.st (x.1.2.loc.w + 2) ρ yv)
    (hoNI : oNo ⟨sixS, i0⟩ = oI) (hoNV : oNo ⟨sixS, i2⟩ = x.1.2.loc.w)
    (hoNO : oNo ⟨sixS, i4⟩ = x.1.2.loc.w + 2)
    (hdep : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = oI →
      (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hokV : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w →
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
        D.st.oracles[(D.mems.get j).id]? = some o ∧
        Send.form csKey (six.get i2).1 (D.mems.get j).id seed 0 = some row0 ∧
        o.sampleRows.toList = [{ row0 with target := tt }] ∧
        bitsZ csKey (six.get i2).1 ≤ seed.z.length ∧ (β : GE) = OnBytes.Slice.readE seed.beta ∧
        ∀ c ∈ seed.z, okE c = true)
    (hfI : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i0).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i0).1))
    (hfV : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i2).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i2).1))
    (hfO : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hwI : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = oI →
      HEq (strOf csKey (six.get i0).1 (six.get i0).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i0))
    (hwV : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w →
      HEq (strOf csKey (six.get i2).1 (six.get i2).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i2))
    (hwO : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w + 2 →
      HEq (strOf csKey (six.get i4).1 (six.get i4).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i4))
    :
    ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i0⟩ ∨ z = ⟨sixS, i2⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft₂ csKey F Fr₃ (nuOf π nl t) (fun q => r q.st) (smpSt csKey oNo fun a : P₃ × St₃ => a.2.st) mem x.2 x.1 (strsOf Fr₃ x.2) s D
            j (xs j) (es j) := by
  intro t ht s rest G0 Ly D hf
  have hd := hdep t ht s rest G0 Ly D hf
  have okV := hokV t ht s rest G0 Ly D hf
  have wI := hwI t ht s rest G0 Ly D hf
  have wV := hwV t ht s rest G0 Ly D hf
  have wO := hwO t ht s rest G0 Ly D hf
  cases ht
  have hm := hgm G0 hf.2.1
  obtain ⟨hlen, hid⟩ := mems_ids π _ s rest G0 Ly D hf
  have h3 : D.mems.length = 3 := by
    rw [hlen]
    simpa using congrArg List.length hm
  have key : ∀ j : Fin D.mems.length, (j.val = 0 ∧ (D.mems.get j).id = oI) ∨
      (j.val = 1 ∧ (D.mems.get j).id = x.1.2.loc.w) ∨
      (j.val = 2 ∧ (D.mems.get j).id = x.1.2.loc.w + 2) := by
    intro j
    have hj := hid j
    rw [← Array.getElem?_toList, hm] at hj
    have hlt := j.isLt
    have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases this with e | e | e
    · rw [e] at hj
      exact Or.inl ⟨e, (Option.some.inj hj).symm⟩
    · rw [e] at hj
      exact Or.inr (Or.inl ⟨e, (Option.some.inj hj).symm⟩)
    · rw [e] at hj
      exact Or.inr (Or.inr ⟨e, (Option.some.inj hj).symm⟩)
  obtain ⟨⟨sI1, sI2, sI3⟩, ⟨sV1, sV2⟩, ⟨sO1, sO2, sO3, sO4⟩⟩ := shapes_32
  refine ⟨(codes_fixed π _ s rest G0 Ly D hf).trans hcod, fun j => ⟨sixS, ix32 j⟩,
    fun j => (six.get (ix32 j)).2, ?_, ?_, ?_⟩
  · intro j j' e
    have e' : ix32 j = ix32 j' := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    have hlt := j.isLt
    have hlt' := j'.isLt
    have c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    have c' : j'.val = 0 ∨ j'.val = 1 ∨ j'.val = 2 := by omega
    rcases c with a | a | a <;> rcases c' with b | b | b
    · exact Fin.ext (a.trans b.symm)
    · rw [ix32_0 j a, ix32_1 j' b] at e'; exact absurd e' (by decide)
    · rw [ix32_0 j a, ix32_2 j' b] at e'; exact absurd e' (by decide)
    · rw [ix32_1 j a, ix32_0 j' b] at e'; exact absurd e' (by decide)
    · exact Fin.ext (a.trans b.symm)
    · rw [ix32_1 j a, ix32_2 j' b] at e'; exact absurd e' (by decide)
    · rw [ix32_2 j a, ix32_0 j' b] at e'; exact absurd e' (by decide)
    · rw [ix32_2 j a, ix32_1 j' b] at e'; exact absurd e' (by decide)
    · exact Fin.ext (a.trans b.symm)
  · rintro z (rfl | rfl | rfl)
    · exact ⟨⟨0, by omega⟩, congrArg (fun k => (⟨sixS, k⟩ : Sound.Mem)) (ix32_0 _ rfl)⟩
    · exact ⟨⟨1, by omega⟩, congrArg (fun k => (⟨sixS, k⟩ : Sound.Mem)) (ix32_1 _ rfl)⟩
    · exact ⟨⟨2, by omega⟩, congrArg (fun k => (⟨sixS, k⟩ : Sound.Mem)) (ix32_2 _ rfl)⟩
  · intro j
    rcases key j with ⟨e, hj⟩ | ⟨e, hj⟩ | ⟨e, hj⟩
    · beta_reduce
      rw [ix32_0 j e]
      obtain ⟨ρ, yv, hs⟩ := hsdI
      exact memberLeft₂_of_seed csKey F Fr₃ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i0⟩
        (six.get i0).1 (six.get i0).2 rfl (tie_six i0) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i0⟩) = _; rw [hoNI]) (tie_six i0).one
        (Or.inl sI1) (Or.inl (Or.inl sI2)) (Or.inr ⟨sI2, sI3, hd j hj⟩) (hfI s rest hf.1)
        (by rw [hj]; exact hmI) (wI j hj)
    · beta_reduce
      rw [ix32_1 j e]
      obtain ⟨ρ, yv, hs⟩ := hsdV
      exact memberLeft₂_of_seed csKey F Fr₃ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i2⟩
        (six.get i2).1 (six.get i2).2 rfl (tie_six i2) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i2⟩) = _; rw [hoNV]) (tie_six i2).one
        (Or.inr (okV j hj)) (Or.inl (Or.inl sV2))
        (Or.inl ⟨sV1, fun h0 => absurd h0 (Nat.pos_iff_ne_zero.1 sV2)⟩) (hfV s rest hf.1)
        (by rw [hj]; exact hmV) (wV j hj)
    · beta_reduce
      rw [ix32_2 j e]
      obtain ⟨ρ, yv, hs⟩ := hsdO
      exact memberLeft₂_of_seed csKey F Fr₃ π _ _ _ mem x.2 x.1 _ _ s rest G0 Ly D hf j ⟨sixS, i4⟩
        (six.get i4).1 (six.get i4).2 rfl (tie_six i4) ρ yv (by rw [hj]; exact hs)
        (by rw [hj]; show K1.smpAt _ _ _ _ (oNo ⟨sixS, i4⟩) = _; rw [hoNO]) (tie_six i4).one
        (Or.inl sO1) (Or.inl (Or.inr sO2)) (Or.inl ⟨sO3, fun _ => sO4⟩) (hfO s rest hf.1)
        (by rw [hj]; exact hmO) (wO j hj)

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₃ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **`back_32_LM₂` (K12Back32.lean) WITH «left» PAID BY `left_32`**: that the two fit is hereby held by
Lean. -/
theorem back_32_LS {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₃ (P₃ × St₃) Cl W) (B : Block St₃ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside Seat.enterOwn Seat.leaveOwn) B)
    (x y : (P₃ × St₃) × Fr₃.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enterOwn x.1.2 = .ok t ∧
      (Seat.leaveOwn x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₃ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hon : on₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) a idx coll src off₂ off₃ t₁ 2 x)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃)
    (hlog : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₃ × St₃ => a.2.st) x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i0 ∨ i = i2 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (oI : ℕ) (hidx : idx = [oI]) (hoI : K₁.orc 0 = some oI) (hnI : K₁.num oI = some 0)
    (hnV : K₁.num x.1.2.loc.w = some 2) (hIn : oI ≠ nOwn x.1.2)
    (hmI : mem oI = some ⟨sixS, i0⟩) (hmV : mem x.1.2.loc.w = some ⟨sixS, i2⟩)
    (hmO : mem (nOwn x.1.2) = some ⟨sixS, i4⟩)
    (hcod : x.1.2.st.codes = csKey)
    (hgm : ∀ G0, x.1.2.st.groups[x.1.2.loc.own]? = some G0 →
      G0.members.toList = [oI, x.1.2.loc.w, x.1.2.loc.w + 2])
    (hsdI : ∃ ρ yv, K1.SeedIs csKey (six.get i0).1 x.1.2.st oI ρ yv)
    (hsdV : ∃ ρ yv, K1.SeedIs csKey (six.get i2).1 x.1.2.st x.1.2.loc.w ρ yv)
    (hsdO : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 x.1.2.st (x.1.2.loc.w + 2) ρ yv)
    (hoNI : oNo ⟨sixS, i0⟩ = oI) (hoNV : oNo ⟨sixS, i2⟩ = x.1.2.loc.w)
    (hoNO : oNo ⟨sixS, i4⟩ = x.1.2.loc.w + 2)
    (hdep : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = oI →
      (D.mems.get j).tsh.logN ≤ s.Z.a)
    (hokV : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w →
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
        D.st.oracles[(D.mems.get j).id]? = some o ∧
        Send.form csKey (six.get i2).1 (D.mems.get j).id seed 0 = some row0 ∧
        o.sampleRows.toList = [{ row0 with target := tt }] ∧
        bitsZ csKey (six.get i2).1 ≤ seed.z.length ∧ (β : GE) = OnBytes.Slice.readE seed.beta ∧
        ∀ c ∈ seed.z, okE c = true)
    (hfI : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i0).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i0).1))
    (hfV : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i2).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i2).1))
    (hfO : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hwI : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = oI →
      HEq (strOf csKey (six.get i0).1 (six.get i0).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i0))
    (hwV : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w →
      HEq (strOf csKey (six.get i2).1 (six.get i2).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i2))
    (hwO : ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = x.1.2.loc.w + 2 →
      HEq (strOf csKey (six.get i4).1 (six.get i4).2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i4))
    (hK : Means.OpenKinds x.1.2.st) (ha : a ≠ 0) (xI : OnBytes.Oracle)
    (hxI : x.1.2.st.oracles[oI]? = some xI) (hsI : xI.sampled = true)
    (hzI : xI.sampleRows.size ≠ 0)
    (hL : L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 3 y) :
    L₃ F Fr₃ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) 2 x :=
  K12Back32.back_32_LM₂ F Fr₃ decT recOf orc₁ tab S K₁ a idx coll src off₂ off₃ t₁ π nl r rdN _ mem rd hrd p
    B hb hal x y τ hout hq hj hp hon
    (left_32 F Fr₃ π nl r oNo mem x oI hmI hmV hmO hcod hgm hsdI hsdV hsdO hoNI hoNV hoNO hdep hokV hfI
      hfV hfO hwI hwV hwO)
    hi hlog told hsm hsh oI hidx hoI hnI hnV hIn hmI hmV hmO hK ha xI hxI hsI hzI hL

/-! ## What falls to the sendings' invariant, and the word in `left_32`'s letters -/

/-- The codes, out of K1.SeedIs's own text. -/
theorem cod_of_seed {cs : Codes} {s : OracleShape} {St : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s St o ρ y) : St.codes = cs :=
  h.1

/-- «The message has its OOD sample stored», out of K1.SeedIs's own text. -/
theorem sampled_of_seed {cs : Codes} {s : OracleShape} {St : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s St o ρ y) :
    ∃ x : OnBytes.Oracle, St.oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0 := by
  obtain ⟨_, x, z, β, t, e1, _, e3, e4, _⟩ := h
  exact ⟨x, e1, e3, by rw [e4]; simp⟩

/-- **The OOD seeds' tie falls to the seeds, at the last chain: a message that the first chain
numbers** (I · V). The like of `sm_of_seed` (K12Members29.lean) at src₃; by
`seedIsS_iff₃_lo` (KeyFillChains.lean). -/
theorem sm_of_seed₃_lo (orc₁ : ℕ → Option ℕ) (oNo : Sound.Mem → ℕ) (i : Fin six.length)
    (hi : numSix i < 3) (o : ℕ) (ho : orc₁ (numSix i) = some o) (hN : oNo ⟨sixS, i⟩ = o)
    (x : P₃ × St₃) (hs : ∃ ρ yv, K1.SeedIs csKey (six.get i).1 x.2.st o ρ yv) :
    ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₃ × St₃ => a.2.st) x sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x ρ σ.2 := by
  obtain ⟨ρ, yv, h⟩ := hs
  obtain ⟨z, e1, e2, e3⟩ :=
    K1.smpAt_of csKey (six.get i).1 (six.get i).2 x.2.st o ρ yv (tie_six i) h
  intro σ hσ
  have e : K1.smpAt csKey (six.get i).1 (six.get i).2 x.2.st (oNo ⟨sixS, i⟩) = some σ := hσ
  rw [hN, e1] at e
  obtain rfl : z = σ := Option.some.inj e
  exact ⟨ρ, e2, (seedIsS_iff₃_lo csKey six numSix orc₁ i hi x ρ z.2).2 ⟨o, ho, yv, h, e3⟩⟩

/-- **… and Omega**, behind the border (`seedIsS_iff₃_own`). -/
theorem sm_of_seed₃_own (orc₁ : ℕ → Option ℕ) (oNo : Sound.Mem → ℕ) (i : Fin six.length)
    (hi : numSix i = 4) (x : P₃ × St₃) (hb : x.2.loc.border = none)
    (hN : oNo ⟨sixS, i⟩ = nOwn x.2)
    (hs : ∃ ρ yv, K1.SeedIs csKey (six.get i).1 x.2.st (nOwn x.2) ρ yv) :
    ∀ σ : (OmAt csKey six i).Smp,
      (smpSt csKey oNo fun a : P₃ × St₃ => a.2.st) x sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i x ρ σ.2 := by
  obtain ⟨ρ, yv, h⟩ := hs
  obtain ⟨z, e1, e2, e3⟩ :=
    K1.smpAt_of csKey (six.get i).1 (six.get i).2 x.2.st (nOwn x.2) ρ yv (tie_six i) h
  intro σ hσ
  have e : K1.smpAt csKey (six.get i).1 (six.get i).2 x.2.st (oNo ⟨sixS, i⟩) = some σ := hσ
  rw [hN, e1] at e
  obtain rfl : z = σ := Option.some.inj e
  exact ⟨ρ, e2, (seedIsS_iff₃_own csKey six numSix orc₁ i hi x hb ρ z.2).2 ⟨yv, h, e3⟩⟩

/-- **The word in `left_32`'s letters, general in the member**: `word_32S` (K12Left32.lean) behind the own
door, at the plan's shape (`member_of_seedIs`: the member's shape is the seed's). The like of
`word_at_29` | `word_at_210`. THE PRICE THAT HAD MOVED COMES BACK: the book's order at the last chain, the
count of its trees, the mask. -/
theorem word_at_32 {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ)
    (hA : AtOk atSix off₂ off₃ t₁) (hω : off₃ t₁ = t₁ + 1) (x : (P₃ × St₃) × Fr₃.E.Str)
    (hmask : x.1.2.loc.mask.isSome = true) (hB : H2K.First.BookOrdW t₁ 1 x.1.2.book)
    (hsz : x.1.2.book.trees.size = t₁ + 1) (i : Fin six.length) (hk : i.val ∈ [0, 2, 4])
    (sh : OracleShape) (e0 : ℕ) (hx : six.get i = (sh, e0)) (o : ℕ) (q : ℕ × ℕ)
    (hq : x.1.2.book.place[o]? = some q) (hat : atSix i.val = (off₃ q.1, q.2))
    (hs : ∃ ρ yv, K1.SeedIs csKey sh x.1.2.st o ρ yv)
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ x.2) i)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, x.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u)
    (hd : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∀ e ∈ Fr₃.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ u.logLength) :
    ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = o →
      HEq (strOf csKey sh e0 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book x.2 (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book x.2 (D.mems.get j).t).2)
        (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₃ x.2) i) := by
  intro t ht s rest G0 Ly D hf j hj
  cases ht
  obtain ⟨ρ, yv, hs⟩ := hs
  have hsh := (member_of_seedIs hf default j (by rw [hj]; exact hs)).1
  subst hsh
  exact K12Left32.word_32S F Fr₃ π t₁ off₂ off₃ hA hω _ hmask s rest G0 Ly D hf hB hsz j i hk q
    (by rw [hj]; exact hq) hat x.2 e0 hx hF hS htold hd

/-- **A member's tree's depth is its code's**: the told tree's log-length (`seatIs_32`'s field log) at the
code's depth (hlog). The like of `dep_at_29` (K12Members29.lean). With «the code's depth is at most the
first stage's mask code's» (a comparison on the list of rounds) it pays `left_32`'s hdep. -/
theorem dep_at_32 {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ)
    (hA : AtOk atSix off₂ off₃ t₁) (hω : off₃ t₁ = t₁ + 1) (x : (P₃ × St₃) × Fr₃.E.Str)
    (hmask : x.1.2.loc.mask.isSome = true) (hB : H2K.First.BookOrdW t₁ 1 x.1.2.book)
    (hsz : x.1.2.book.trees.size = t₁ + 1) (i : Fin six.length) (hk : i.val ∈ [0, 2, 4])
    (o : ℕ) (q : ℕ × ℕ) (hq : x.1.2.book.place[o]? = some q)
    (hat : atSix i.val = (off₃ q.1, q.2))
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hlog : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      u.logLength = aOf csKey (six.get i).1)
    (htold : ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∃ T, x.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u) :
    ∀ t, Seat.enterOwn x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
      (D.mems.get j).id = o → (D.mems.get j).tsh.logN = aOf csKey (six.get i).1 := by
  intro t ht s rest G0 Ly D hf j hj
  cases ht
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 told
  exact (K12Left32.seatIs_32 π t₁ off₂ off₃ hA hω _ hmask s rest G0 Ly D hf hB hsz j i.val hk q
    (by rw [hj]; exact hq) hat u (htold u hu)).log.trans (hlog u hu)

/-! ## «V's OOD seed's point is canonical», carried to the plain data's statement -/

section Carried
open Johnson.RunOne.KeyMsg (SeedOk seedOk_reads)

/-! The four next are `seedIs_of_part` · `seedIs_begun` · `seedIs_made` · `seedIs_fixes`
(Johnson/Desc/Sound/SeedAtKind.lean), statement and proof, with `SeedOk`
(Johnson/RunOne/KeySeedOk.lean: K1.SeedIs with one conjunct more) in K1.SeedIs's place: made by program out of
that file's text; the one conjunct is handed on. KIN, SAID: they belong beside `SeedOk.travels`. -/

/-- **Kept where the codes and, at the number, the shape, the mark and the sample rows stay.** -/
theorem seedOk_of_part {cs : Codes} {s : OracleShape} {A B : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedOk cs s A o ρ y)
    (hc : B.codes = A.codes)
    (hp : (B.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (A.oracles[o]?).map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) :
    SeedOk cs s B o ρ y := by
  obtain ⟨h0, x, z, β, t, hx, h1, h2, h3, h4, h5, h6⟩ := h
  rw [hx] at hp
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨hc.trans h0, x', z, β, t, hx', e1.trans h1, e2.trans h2, e3.trans h3, h4, h5, h6⟩

/-- Past the beginning of a test. -/
theorem seedOk_begun {cs : Codes} {s : OracleShape} {S : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedOk cs s S o ρ y) (g : ℕ) (G : OnBytes.Group) :
    SeedOk cs s (begun S g G) o ρ y := by
  refine seedOk_of_part h (begun_codes S g G) ?_
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e, Option.map_map]
  congr 1
  funext x
  show ((if o ∈ G.members.toList then shut x else x).shape,
    (if o ∈ G.members.toList then shut x else x).sampled,
    (if o ∈ G.members.toList then shut x else x).sampleRows) = _
  split <;> rfl

/-- Into the plain data. -/
theorem seedOk_made {cs : Codes} {s : OracleShape} {p : P12} {t : T12} {a : Fmt.M1.Stage}
    {L : GroupLayout} {D : H2K.First.Plain} (hm : H2K.First.Made p t a L D) {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedOk cs s t.st o ρ y) :
    SeedOk cs s D.st o ρ y := by
  have ho : o < t.st.oracles.size := by
    obtain ⟨_, x, _, _, _, hx, _⟩ := h
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hx
    cases hx
  exact seedOk_of_part h (H2K.Pin.codes_made hm).symm (by rw [H2K.Pin.oracle_made hm o ho])

/-- **From the kind's record to whatever the record fixes.** -/
theorem seedOk_fixes {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedOk cs s t.st o ρ y) :
    SeedOk cs s D.st o ρ y :=
  seedOk_made (H2K.First.made_of π _ a Ly D (hf.2.2.2 row₀)) (seedOk_begun h t.g G0)

/-- **`left_32`'s hokV | `MemberLeft₂`'s new conjunct, from SeedOk at the state behind the door in.** -/
theorem okV_of_seedOk {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain}
    (hf : Fixes π t a rest G0 Ly D) (hT : K1.Tie cs s) {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedOk cs s t.st o ρ y) :
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[o]? = some x ∧ Send.form cs s o seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ cs s ≤ seed.z.length ∧ (β : GE) = OnBytes.Slice.readE seed.beta ∧
      ∀ c ∈ seed.z, okE c = true := by
  obtain ⟨x, seed, row0, tt, e1, _, _, e4, e5, hr, _, _, hok⟩ :=
    seedOk_reads hT (seedOk_fixes hf default h)
  exact ⟨x, seed, row0, tt, ρ.2, e1, e4, e5, hr.long, hr.factor.symm, hok⟩

end Carried

end Johnson.RunOne.Law.K12Members32

#print axioms Johnson.RunOne.Law.K12Members32.memberLeft₂_of_seed
#print axioms Johnson.RunOne.Law.K12Members32.shapes_32
#print axioms Johnson.RunOne.Law.K12Members32.left_32
#print axioms Johnson.RunOne.Law.K12Members32.back_32_LS
#print axioms Johnson.RunOne.Law.K12Members32.cod_of_seed
#print axioms Johnson.RunOne.Law.K12Members32.sampled_of_seed
#print axioms Johnson.RunOne.Law.K12Members32.sm_of_seed₃_lo
#print axioms Johnson.RunOne.Law.K12Members32.sm_of_seed₃_own
#print axioms Johnson.RunOne.Law.K12Members32.word_at_32
#print axioms Johnson.RunOne.Law.K12Members32.dep_at_32
#print axioms Johnson.RunOne.Law.K12Members32.seedOk_fixes
#print axioms Johnson.RunOne.Law.K12Members32.okV_of_seedOk
