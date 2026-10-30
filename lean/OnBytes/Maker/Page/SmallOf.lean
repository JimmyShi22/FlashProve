-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/SmallOf.lean: the bounds that the hash's domain asks of a file's three
descriptions and of the file (`SmallThree`, OnBytes/Maker/Page/AtOracle.lean) follow from the record
of the reading, from two tests on the plain data of the dry runs' three lists, and from the verifier
program's own limit on the length of a file.

Statements and proofs. `OnBytes.Tie.smallFX` asks: bounds on the parameter bytes, the statement, the
number of rounds and the configuration's digest; of each opened tree's shape a number, a depth and a
width within bounds, and the mark "stored" only with the number 0; of a tree taken over a start of
32 bytes; the like of the stored tables; and a bound on the file's length. A description that is
returned has passed the strict reader's conditions (`Fmt.SpecX.ok`), which hold all of these but
two: that a tree taken over does not bear the mark "stored", and the file's length. The first
follows from two tests on the data: no tree that the chains send bears the mark (of `okAt` the proof
uses three parts), and the shapes in the rounds' data are those of the data's table (`shapesFit`).
The second follows from `Shell.fileLimit`.

Main names:
  `smallFX_of_ok`: at one description in order, none of whose opened trees bears the mark.
  `table_plain`: no tree of the data's table bears the mark.
  `opens_plain`: so no opened tree of a description that the data fit.
  `small_of_read`: `SmallThree` at the record of a reading and any file within the limit.
  `small_keyGood`: at a good reading of a key file (`KeyGood`), at every file of the length that the
    reading fixes.
No letter stands under "there is".
Limits: the two tests are not shown here. They stand at the three lists that the dry runs give at
the reading's key, the third at made-up names: not at the rounds under which the third chain was
read. `small_of_read` asks beside them the first description's equation, that the first block's dry
run leaves a book of its own chain's trees, the dry runs' equation at the reading's key and one
number of bytes of a salt for the three chains; `small_keyGood` asks the plan, a fixed key with the
item 0 that fits, and the dry runs at it. For a proof file the limit on the file's length is a
premise of `small_of_read`. Nothing on soundness.


-/
import OnBytes.Maker.Page.OwesOfGood
import OnBytes.Tie.StoredMain
import OnBytes.Shell.Ask
import Run.OneIsTypedTop

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- A file within the program's limit is within the hash's bound on a message. -/
theorem limit_small {b : ByteArray} (h : b.size ≤ Shell.fileLimit) :
    b.size + 16 ≤ 2 ^ 32 - 144 := by
  unfold Shell.fileLimit at h
  omega

/-- **The bounds at one description in order, none of whose opened trees bears the mark "stored".**
-/
theorem smallFX_of_ok (S : Fmt.SpecX) (hS : S.ok = true) (b : ByteArray)
    (hb : b.size ≤ Shell.fileLimit)
    (hg : ∀ r ∈ S.base.rounds, ∀ o ∈ r.opens, o.1.stored = false) : smallFX S b = true := by
  have hB : S.base.ok = true := specX_base S hS
  have hsm := Fmt.ok_small hB
  unfold Fmt.Spec.small at hsm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsm
  obtain ⟨⟨⟨⟨s1, s2⟩, -⟩, s4⟩, s5⟩ := hsm
  have htr := Fmt.ok_trees hB
  have hdp := Fmt.ok_depth hB
  simp only [List.all_eq_true, decide_eq_true_eq] at htr hdp
  have hF : smallF S.base b = true := by
    unfold Run.smallF Run.smallB
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨s1, s2⟩, limit_small hb⟩, s5⟩, Fmt.ok_cfg hB⟩, fun r hr o ho => ?_⟩
    obtain ⟨af, se, hro⟩ := roundsOk_mem _ _ _ S.base.rounds _ _ (Fmt.ok_rounds hB) r hr
    unfold Fmt.Round.ok at hro
    simp only [Bool.and_eq_true, List.all_eq_true] at hro
    have hlast := (hro.2 o ho).2
    have hd : o.1.a ≤ 48 := by
      have := hdp r hr o ho
      unfold Fmt.depthOK at this
      exact of_decide_eq_true this
    unfold Run.smallO Run.smallSh
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨htr r hr o ho, hd⟩, (s4 r hr o ho).1⟩, (s4 r hr o ho).2⟩,
      Or.inl (hg r hr o ho)⟩, ?_⟩
    cases hsrc : o.2 with
    | own n => rfl
    | given root start =>
      rw [hsrc] at hlast
      exact (Bool.and_eq_true_iff.1 hlast).2
  unfold smallFX
  rw [Bool.and_eq_true, hF]
  refine ⟨rfl, ?_⟩
  rw [List.all_eq_true]
  intro ts hts
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at ht
    cases ht
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, k3⟩, k4⟩, k5⟩, k6⟩, -⟩, -⟩, -⟩ := h.2 t ht
    unfold Run.smallSh
    unfold Fmt.depthOK at k3
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨by rw [k6]; decide, of_decide_eq_true k3⟩, k4⟩, k5⟩, Or.inr k6⟩

/-- A tree that one of the three stretches' rounds sends does not bear the mark. -/
theorem sent_plain {D : WholeD} (h : D.runFit = true) {ds : List RDT}
    (hds : ∀ d ∈ ds, d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃)) {n : ℕ} {sh : Fmt.Shape}
    (hs : treeShT ds n = some sh) : sh.stored = false := by
  obtain ⟨d, hd, hm⟩ := mem_of_treeShT ds n sh hs
  unfold WholeD.runFit at h
  have := List.all_eq_true.1 (List.all_eq_true.1 h d (hds d hd)) sh hm
  simpa using this

/-- **No tree of the data's table bears the mark "stored".** -/
theorem table_plain {a : ℕ} {W : Three.Whole} (hrun : (WholeD.of a W).runFit = true)
    (hsh : shapesFit a W = true) :
    ∀ (j : ℕ) t, W.table[j]? = some t → t.shape.stored = false := by
  intro j t ht
  have hj : j < W.table.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at ht
    cases ht
  unfold shapesFit at hsh
  have e := eq_of_beq (List.all_eq_true.1 hsh j (List.mem_range.2 hj))
  rw [ht] at e
  have e' : (WholeD.of a W).shape j = some t.shape := e
  unfold WholeD.shape at e'
  split at e'
  · exact sent_plain hrun (fun d hd => List.mem_append_left _ hd) e'
  · split at e'
    · exact sent_plain hrun
        (fun d hd => List.mem_append_right _ (List.mem_append_left _ hd)) e'
    · exact sent_plain hrun
        (fun d hd => List.mem_append_right _ (List.mem_append_right _ hd)) e'

/-- Each member of the left list of a related pair of lists has a partner. -/
theorem forall₂_left {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ P l m → ∀ x ∈ l, ∃ y, P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, h⟩
    · exact forall₂_left t x hx

/-- **No opened tree of a description that the data fit bears the mark.** -/
theorem opens_plain {W : Three.Whole}
    (hp : ∀ (j : ℕ) t, W.table[j]? = some t → t.shape.stored = false) {S : Fmt.SpecX}
    (hS : S.ok = true) {ds : List Three.RDL}
    (F : DataFits W (S.base.rounds.zip S.stored) ds) :
    ∀ r ∈ S.base.rounds, ∀ o ∈ r.opens, o.1.stored = false := by
  intro r hr o ho
  obtain ⟨ts, hz⟩ := mem_zip_left S.base.rounds S.stored (specX_len S hS).symm r hr
  obtain ⟨d, -, hd⟩ := forall₂_left F (keyOf (r, ts)) (List.mem_map_of_mem hz)
  obtain ⟨j, t, ht, e⟩ := forall₂_left hd o.1 (List.mem_map_of_mem ho)
  rw [← e]
  exact hp j t ht

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **The bounds, at the record of a reading and any file b within the program's limit.** -/
theorem small_of_read (a sb : ℕ)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true)
    (hsh : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb) (b : ByteArray)
    (hb : b.size ≤ Shell.fileLimit) : SmallThree S₁ S₂ S₃ b := by
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit (okAt_parts hok).stored
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of (okAt_parts hok).fits hS₁ T.shared_spec T.second_spec (alike_shapes N)
      (alike_stored N) s₁ s₂ s₃ a₁ a₂ a₃
  have hp := table_plain (okAt_parts hok).run hsh
  have k₁ : S₁.ok = true := Params.Given.describe_ok hS₁
  have k₂ : S₂.ok = true := Params.Given.describe_ok T.shared_spec
  have k₃ : S₃.ok = true := Params.Given.describe_ok T.second_spec
  exact ⟨smallFX_of_ok S₁ k₁ b hb (opens_plain hp k₁ F.d₁),
    smallFX_of_ok S₂ k₂ b hb (opens_plain hp k₂ F.d₂),
    smallFX_of_ok S₃ k₃ b hb (opens_plain hp k₃ F.d₃)⟩

end

/-- **At a good reading of a key file**: at every file of the length that the reading fixes. -/
theorem small_keyGood (u : KeyPub) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R)
    (d : Params.TableName × ChainsData) (hg : KeyGood u d) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    ∀ file : ByteArray, file.size = d.2.r.second.next →
      SmallThree d.2.S1 d.2.S2 d.2.S3 file := by
  intro file hsz
  have hR' := good_dry3 u p hp key₀ h0 hf R hR d hg
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  obtain ⟨F, e1, e2, e3, ho, hdd⟩ := hg
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F d.1 ho
  rw [e1, e2, e3] at hp' hd'
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d.2 = d' := congrArg Prod.snd (Option.some.inj (hdd.symm.trans hd'))
  have hlim : F.key.size ≤ Shell.fileLimit := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, hz, -⟩ := ho
    exact hz
  have Tr := T.toRead
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement d.1) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  unfold dryKey at hR'
  rw [Tr.first_dry] at hR'
  have hd3 : Three.dry3 (Key.tailPublic p.chains.key d.1) d.2.r.key (d.2.rounds1, d.2.dry) =
      some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
  obtain ⟨-, b₁⟩ := key_own p.chains.key.oneTime Tr.first_dry
  exact small_of_read a p.chains.key.oneTime.given.plan.salt Tr hS' b₁ R₃ hd3 hok hsh rfl
    s₂.salt.symm s₃.salt.symm file (by rw [hsz, Tr.whole]; exact hlim)

end OnBytes.Maker.Page
