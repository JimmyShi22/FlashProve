-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingAlike.lean: the openings in the typing of a whole file are as the compiled
verifier's strict format asks, where the verifier's messages give the draws that were read up to the
digests drawn.

A round of the kind "sealed" draws a digest, and in the joined protocol of a file the typed
verifier's message of the second chain's last round need not hold the digest that the reader has
drawn there: how typed queries are spelled as hash calls decides it. So an equation of the lists of
draws is not expected to hold for the second chain (a reading of the spelling that is in use; no law
here shows it). Which positions are read hangs on the drawn positions alone. So the premise here is:
equal but for the digests, round by round (`DrawnAlike`, OnBytes/TypedOracleCompiler/Laws/LawAlike.lean), in the
form of `HoldsA` (OnBytes/Maker/ViewsAlike.lean). An equation gives it (`LAlike.refl`).

  `wantsRead`, `wantsAll_alike`   the wants of the three chains, from the draws as read.
  `tree_wanted_read`, `table_wanted_read`   what these ask for is what the file's openings list.
  `opensFitA₁`, `opensFitA₂`, `opensFitA₃`, `extFitA`   the openings of the three stretches, and of
                       the stored table, stand exactly where the file's reduction reads, and have
                       salts and paths of the right lengths.
  `opened_typeFileA`   **the four records of the strict format at a value of `typeFile`.**
  `opened_atA`         the same from the three chains' values under g, with the test `saltsFit` in
                       the place of the premise on the stored tables' salts.
  `opened_wholeA`      from the three chains' values under g: the one record over the whole file,
                       and the stored table's.

The premises. The tests `shapesFit`, `sealBare`, `saltsFit` on the data. `ListedAsDrawn` for each
chain: a law of the reader (OnBytes/Maker/ReadFacts.lean). Each sender's run's value and the digest
cfg have 32 bytes. The verifier's messages give, chain by chain, the draws as read but for the
digests: the tie of the hash chain. That `typeFile` returns a value. For `opened_typeFileA`:
`RtFlagsAll` and `SentK` at the three chains' values, which stand under no run there; `opened_atA`
has these six from the runs (`flags₁_of_det` and its like) and asks in their place that the three
chains return values under g. None is shown here. What the transcript holds, under the same premise
on the draws, is in OnBytes/Maker/AcceptAtA.lean.

Not claimed. That the verifier's messages give the draws as read. Nothing on soundness.


-/
import OnBytes.Maker.TypingAt
import OnBytes.Maker.ViewsAlike

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ OnBytes.TwoLaws

/-! ## What is wanted -/

/-- The wants of the three chains, from the draws as read. -/
def wantsRead (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) : List Want :=
  wantsOf a (WholeD.of a W).depth (W.ds₁.dropLast.map rdtOf)
      (r.first.out.rounds.toList.dropLast.map (·.drawn)) ++
    (wantsOf a (WholeD.of a W).depth (W.ds₂.map rdtOf)
        (r.shared.out.rounds.toList.map (·.drawn)) ++
      wantsOf a (WholeD.of a W).depth (W.ds₃.map rdtOf)
        (r.second.out.rounds.toList.map (·.drawn)))

section Wants
variable {C : CK} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

theorem wantsAll_alike (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₁ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₁ ρ)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₂ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₂ ρ)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₃ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₃ ρ))) :
    wantsAll C (WholeD.of a W) tF tJ t3 ρ = wantsRead a W r := by
  unfold wantsAll wants₁ wants₂ wants₃ wantsRead
  rw [← wantsOf_poss _ _ _ hd₁, ← wantsOf_poss _ _ _ hd₂, ← wantsOf_poss _ _ _ hd₃]
  rfl

theorem tree_wanted_read (htabs : TabsHold W sb r tabs) (hshape : shapesFit a W = true)
    (hseal : sealBare W = true) (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList) (j x : ℕ) :
    Want.tree j x ∈ wantsRead a W r ↔ ∃ z, (j, z) ∈ ownRowsW W r ∧ x ∈ z.2.1 := by
  have hfit := htabs.fits
  unfold fitsW at hfit
  simp only [Bool.and_eq_true] at hfit
  obtain ⟨n₁, o₁⟩ := roundsFit_spec hfit.1.1
  obtain ⟨n₂, o₂⟩ := roundsFit_spec hfit.1.2
  obtain ⟨n₃, o₃⟩ := roundsFit_spec hfit.2
  have hdep : ∀ q ∈ ownRowsW W r, (WholeD.of a W).depth q.1 = some q.2.1.a := by
    rintro ⟨j, z⟩ hz
    obtain ⟨t, ht, e1, -⟩ := htabs.row j z hz
    rw [WholeD.depth_shape, shapesFit_at hshape ht, e1]
    rfl
  have less := mem_zip_dropLast W.ds₁ r.first.out.rounds.toList n₁
  have w₁ := tree_wanted a (WholeD.of a W).depth W.ds₁.dropLast
    r.first.out.rounds.toList.dropLast (by rw [List.length_dropLast, List.length_dropLast, n₁])
    (fun p hp => o₁ p (less p hp))
    (fun p hp q hq => hdep q (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, less p hp, hq⟩)))
    (fun p hp => hl₁ p (less p hp)) j x
  have w₂ := tree_wanted a (WholeD.of a W).depth W.ds₂ r.shared.out.rounds.toList n₂ o₂
    (fun p hp q hq => hdep q (List.mem_append_right _
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, hq⟩)))) hl₂ j x
  have w₃ := tree_wanted a (WholeD.of a W).depth W.ds₃ r.second.out.rounds.toList n₃ o₃
    (fun p hp q hq => hdep q (List.mem_append_right _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, hq⟩)))) hl₃ j x
  rw [← ownRows_less hseal r.first.out n₁] at w₁
  unfold wantsRead
  rw [List.mem_append, List.mem_append, w₁, w₂, w₃]
  unfold ownRowsW
  constructor
  · rintro (⟨z, hz, hx⟩ | ⟨z, hz, hx⟩ | ⟨z, hz, hx⟩)
    · exact ⟨z, List.mem_append_left _ hz, hx⟩
    · exact ⟨z, List.mem_append_right _ (List.mem_append_left _ hz), hx⟩
    · exact ⟨z, List.mem_append_right _ (List.mem_append_right _ hz), hx⟩
  · rintro ⟨z, hz, hx⟩
    rcases List.mem_append.1 hz with h | h
    · exact Or.inl ⟨z, h, hx⟩
    · rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inl ⟨z, h, hx⟩)
      · exact Or.inr (Or.inr ⟨z, h, hx⟩)

theorem table_wanted_read (hfits : fitsW W r = true) (hseal : sealBare W = true)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList) (x : ℕ) :
    (∃ item, Want.table item x ∈ wantsRead a W r) ↔
      ∃ t z, (t, z) ∈ storedRowsW W r ∧ x ∈ z.2.1 := by
  have hfit := hfits
  unfold fitsW at hfit
  simp only [Bool.and_eq_true] at hfit
  obtain ⟨n₁, o₁⟩ := roundsFit_spec hfit.1.1
  obtain ⟨n₂, o₂⟩ := roundsFit_spec hfit.1.2
  obtain ⟨n₃, o₃⟩ := roundsFit_spec hfit.2
  have less := mem_zip_dropLast W.ds₁ r.first.out.rounds.toList n₁
  have w₁ := table_wanted a (WholeD.of a W).depth W.ds₁.dropLast
    r.first.out.rounds.toList.dropLast (by rw [List.length_dropLast, List.length_dropLast, n₁])
    (fun p hp => o₁ p (less p hp)) (fun p hp => hl₁ p (less p hp)) x
  have w₂ := table_wanted a (WholeD.of a W).depth W.ds₂ r.shared.out.rounds.toList n₂ o₂ hl₂ x
  have w₃ := table_wanted a (WholeD.of a W).depth W.ds₃ r.second.out.rounds.toList n₃ o₃ hl₃ x
  rw [← storedRows_less hseal r.first.out n₁] at w₁
  unfold wantsRead storedRowsW
  constructor
  · rintro ⟨item, h⟩
    rcases List.mem_append.1 h with h | h
    · obtain ⟨t, z, hz, hx⟩ := w₁.1 ⟨item, h⟩
      exact ⟨t, z, List.mem_append_left _ hz, hx⟩
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨t, z, hz, hx⟩ := w₂.1 ⟨item, h⟩
        exact ⟨t, z, List.mem_append_right _ (List.mem_append_left _ hz), hx⟩
      · obtain ⟨t, z, hz, hx⟩ := w₃.1 ⟨item, h⟩
        exact ⟨t, z, List.mem_append_right _ (List.mem_append_right _ hz), hx⟩
  · rintro ⟨t, z, hz, hx⟩
    rcases List.mem_append.1 hz with h | h
    · obtain ⟨item, hi⟩ := w₁.2 ⟨t, z, h, hx⟩
      exact ⟨item, List.mem_append_left _ hi⟩
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨item, hi⟩ := w₂.2 ⟨t, z, h, hx⟩
        exact ⟨item, List.mem_append_right _ (List.mem_append_left _ hi)⟩
      · obtain ⟨item, hi⟩ := w₃.2 ⟨t, z, h, hx⟩
        exact ⟨item, List.mem_append_right _ (List.mem_append_right _ hi)⟩

end Wants

/-! ## The four conditions, stretch by stretch -/

section Fit
variable {C : CK} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  (htabs : TabsHold W sb r tabs) (hback : TabsBack W sb r tabs) (hshape : shapesFit a W = true)
  (hseal : sealBare W = true) (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32)
  (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
  (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
  (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
  (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ t3).sh)
  (hw : wantsAll C (WholeD.of a W) tF tJ t3 ρ = wantsRead a W r)

include htabs hback hshape hseal hrun hl₁ hl₂ hl₃ hw

theorem opensFitA₁ :
    OpensFit C (WholeD.of a W).ds₁ 0 tabs (256 + 8 * sb) fun q =>
      (chainsOf C (WholeD.of a W) tF tJ t3).i₁ q ∈
        (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ := by
  have h := opensFit_of C a W sb r tabs (WholeD.of a W).ds₁ 0
    (fun j x => Want.tree j x ∈ wantsRead a W r) htabs hback hshape hrun
    (shape₁ C (WholeD.of a W)) (tree_wanted_read htabs hshape hseal hl₁ hl₂ hl₃)
  have e : (fun q => (chainsOf C (WholeD.of a W) tF tJ t3).i₁ q ∈
      (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ) = fun q =>
      Want.tree (0 + treeAt C (WholeD.of a W).ds₁ q) (leafAt C (WholeD.of a W).ds₁ q) ∈
        wantsRead a W r :=
    funext fun q => by
      rw [Nat.zero_add, ← hw]
      exact propext (reads₁ C _ tF tJ t3 silent run ρ q)
  rw [e]
  exact h

theorem opensFitA₂ :
    OpensFit C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs (256 + 8 * sb) fun q =>
      (chainsOf C (WholeD.of a W) tF tJ t3).i₂ q ∈
        (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ := by
  have h := opensFit_of C a W sb r tabs (WholeD.of a W).ds₂ (WholeD.of a W).t₁
    (fun j x => Want.tree j x ∈ wantsRead a W r) htabs hback hshape hrun
    (shape₂ C (WholeD.of a W)) (tree_wanted_read htabs hshape hseal hl₁ hl₂ hl₃)
  have e : (fun q => (chainsOf C (WholeD.of a W) tF tJ t3).i₂ q ∈
      (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ) = fun q =>
      Want.tree ((WholeD.of a W).t₁ + treeAt C (WholeD.of a W).ds₂ q)
        (leafAt C (WholeD.of a W).ds₂ q) ∈ wantsRead a W r :=
    funext fun q => by
      rw [← hw]
      exact propext (reads₂ C _ tF tJ t3 silent run ρ q)
  rw [e]
  exact h

theorem opensFitA₃ :
    OpensFit C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs (256 + 8 * sb)
      fun q => (chainsOf C (WholeD.of a W) tF tJ t3).i₃ q ∈
        (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ := by
  have h := opensFit_of C a W sb r tabs (WholeD.of a W).ds₃
    ((WholeD.of a W).t₁ + (WholeD.of a W).t₂)
    (fun j x => Want.tree j x ∈ wantsRead a W r) htabs hback hshape hrun
    (shape₃ C (WholeD.of a W)) (tree_wanted_read htabs hshape hseal hl₁ hl₂ hl₃)
  have e : (fun q => (chainsOf C (WholeD.of a W) tF tJ t3).i₃ q ∈
      (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).reads ρ) = fun q =>
      Want.tree ((WholeD.of a W).t₁ + (WholeD.of a W).t₂ + treeAt C (WholeD.of a W).ds₃ q)
        (leafAt C (WholeD.of a W).ds₃ q) ∈ wantsRead a W r :=
    funext fun q => by
      rw [← hw]
      exact propext (reads₃ C _ tF tJ t3 silent run ρ q)
  rw [e]
  exact h

end Fit

section Ext
variable {C : CK} {a : ℕ} {W : Three.Whole} {sb : ℕ} {cfg : ByteArray} {r : Proof.TailRead}
  {etab : List (ℕ × Row3)} {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem extFitA (hext : ExtHolds a W r etab) (hback : ExtBack cfg W r etab)
    (hfits : fitsW W r = true) (hseal : sealBare W = true) (hcfg : cfg.size = 32)
    (hsalt : ∀ t z, (t, z) ∈ storedRowsW W r → t.salt = sb)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (hw : wantsAll C (WholeD.of a W) tF tJ t3 ρ = wantsRead a W r) :
    (∀ (p : (oneExternalString (2 ^ a) SgX).Pos) (op : Opening 256 SgX),
      atT (fun c => some (p.val, c)) etab p.val = some op →
        p ∈ (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).extReads ρ ∧
          op.salt.length = 256 + 8 * sb ∧ op.path.length = a) ∧
      ∀ p : (oneExternalString (2 ^ a) SgX).Pos,
        p ∈ (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).extReads ρ →
          (atT (fun c => (some (p.val, c) : Option SgX)) etab p.val).isSome = true := by
  have hwt := table_wanted_read (a := a) hfits hseal hl₁ hl₂ hl₃
  rw [← hw] at hwt
  refine ⟨fun p op h => ?_, fun p h => ?_⟩
  · unfold atT at h
    cases hl : etab.lookup p.val with
    | none => rw [hl] at h; cases h
    | some row =>
      obtain ⟨c, s, pt⟩ := row
      rw [hl] at h
      obtain rfl : (⟨(p.val, c), s, pt⟩ : Opening 256 SgX) = op := Option.some.inj h
      obtain ⟨t, z, s0, hz, hm, hs0, hs, hp⟩ := hback _ _ _ _ hl
      obtain ⟨e1, e2, -, -⟩ := hext.row t z hz
      refine ⟨(mem_extReads C _ tF tJ t3 silent run ρ p).2
        ((hwt p.val).2 ⟨t, z, hz, (List.of_mem_zip hm).1⟩), ?_, ?_⟩
      · show s.length = _
        rw [hs, length_leafSalt, hcfg, hs0, hsalt t z hz]
      · show pt.length = _
        rw [hp, e1, e2]
  · obtain ⟨t, z, hz, hx⟩ := (hwt p.val).1 ((mem_extReads C _ tF tJ t3 silent run ρ p).1 h)
    obtain ⟨-, -, -, hok⟩ := hext.row t z hz
    obtain ⟨c, hc⟩ := exists_zip_of_mem z.2.1 z.2.2.cols _
      (Nat.le_of_eq (TieTree.ok_spec (asOpenB z) _ _ hok).1.symm) hx
    obtain ⟨s, pt, hl⟩ := hext.look t z hz _ c hc
    unfold atT
    rw [hl]
    rfl

end Ext

/-! ## The four records at a value of the typing -/

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The four records at a value of `typeFile`**, the draws but for the digests. -/
theorem opened_typeFileA (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (hF₁ : RtFlagsAll _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
      (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) a'.2.1)
    (hF₂ : RtFlagsAll _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
      (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) b'.2.1)
    (hF₃ : RtFlagsAll _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
      (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) e'.2.1)
    (hK₁ : SentK _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁ a'.2.1)
    (hK₂ : SentK _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂ b'.2.1)
    (hK₃ : SentK _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃ e'.2.1)
    (hshape : shapesFit a W = true) (hseal : sealBare W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32) (hcfg : cfg.size = 32)
    (hsalt : ∀ t z, (t, z) ∈ storedRowsW W r → t.salt = sb)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₁ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₁ (glue a' b' e').1)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₂ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₂ (glue a' b' e').1)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₃
        ((chainsOf C (WholeD.of a W) tF tJ t3).rho₃ (glue a' b' e').1))) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
        (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) a'.2.1
        (rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
        (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) b'.2.1
        (rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
        (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) e'.2.1
        (rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      OpenedE (256 + 8 * sb) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).maxDepth
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext
        (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1) π.ext := by
  obtain ⟨tabs, etab, ht, hE, hx, o1, o2, o3⟩ :=
    typeFile_opens C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  have htabs := tabsWFull_holds ht
  have hback := tabsWFull_back ht
  have hw := wantsAll_alike tF tJ t3 (glue a' b' e').1 hd₁ hd₂ hd₃
  have w1 : wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₁_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  have w2 : wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₂_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  have w3 : wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₃_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  rw [w1] at hF₁
  rw [w2] at hF₂
  rw [w3] at hF₃
  have s1 : SentLo C (WholeD.of a W).ds₁ a'.2.1.2 := sentLo_of C K chal _ _ hF₁.2 hK₁.2.2
  have s2 : SentSh C (WholeD.of a W).ds₂ b'.2.1.2 := sentSh_of C K chal _ _ hF₂.2 hK₂.2.2
  have s3 : SentLo C (WholeD.of a W).ds₃ e'.2.1.2 := sentLo_of C K chal _ _ hF₃.2 hK₃.2.2
  have f1 := opensFitA₁ tF tJ t3 silent run htabs hback hshape hseal hrun hl₁ hl₂ hl₃
    (glue a' b' e').1 hw
  have f2 := opensFitA₂ tF tJ t3 silent run htabs hback hshape hseal hrun hl₁ hl₂ hl₃
    (glue a' b' e').1 hw
  have f3 := opensFitA₃ tF tJ t3 silent run htabs hback hshape hseal hrun hl₁ hl₂ hl₃
    (glue a' b' e').1 hw
  obtain ⟨x1, x2⟩ := extFitA tF tJ t3 silent run (extTabWFull_holds hE) (extTabWFull_back hE)
    htabs.fits hseal hcfg hsalt hl₁ hl₂ hl₃ (glue a' b' e').1 hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [w1, o1]
    refine opened_lo C K chal tF _ _ _ 0 tabs _ a'.2.1 _ s1 ?_
    exact ⟨fun q op hq => ⟨decide_eq_true (f1.only q op hq).1, (f1.only q op hq).2⟩,
      fun q hq => f1.all q (of_decide_eq_true hq), f1.path⟩
  · rw [w2, o2]
    refine opened_sh C K chal tJ _ _ _ _ tabs _ b'.2.1 _ s2 ?_
    exact ⟨fun q op hq => ⟨decide_eq_true (f2.only q op hq).1, (f2.only q op hq).2⟩,
      fun q hq => f2.all q (of_decide_eq_true hq), f2.path⟩
  · rw [w3, o3]
    refine opened_lo C K chal t3 _ _ _ _ tabs _ e'.2.1 _ s3 ?_
    exact ⟨fun q op hq => ⟨decide_eq_true (f3.only q op hq).1, (f3.only q op hq).2⟩,
      fun q hq => f3.all q (of_decide_eq_true hq), f3.path⟩
  · rw [hx]
    exact
      { only := fun p _ op hp => ⟨decide_eq_true (x1 p op hp).1, (x1 p op hp).2.1⟩
        all := fun p _ hp => x2 p (of_decide_eq_true hp)
        path := fun p _ op _ hp => (x1 p op hp).2.2
        leaf := fun p => p.isLt
        depth := le_max_left _ _ }

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 (K + 1) L)) {t : Tag}
  {embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

/-- **The same from the three chains' values under g**, with the test `saltsFit`. -/
theorem opened_atA (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a' b').det g =
      some e')
    (hshape : shapesFit a W = true) (hseal : sealBare W = true) (hsalts : saltsFit sb W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32) (hcfg : cfg.size = 32)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₁ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₁ (glue a' b' e').1)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₂ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₂ (glue a' b' e').1)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₃
        ((chainsOf C (WholeD.of a W) tF tJ t3).rho₃ (glue a' b' e').1))) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
        (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) a'.2.1
        (rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
        (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) b'.2.1
        (rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
        (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) e'.2.1
        (rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      OpenedE (256 + 8 * sb) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).maxDepth
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext
        (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1) π.ext :=
  opened_typeFileA C K chal a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h x a' b' e'
    (flags₁_of_det g h₁).1 (flags₂_of_det g h₂).1 (flags₃_of_det g h₃).1 (flags₁_of_det g h₁).2
    (flags₂_of_det g h₂).2 (flags₃_of_det g h₃).2 hshape hseal hrun hcfg (saltsFit_spec hsalts r)
    hl₁ hl₂ hl₃ hd₁ hd₂ hd₃

/-- **The one record over the whole file, and the stored table's**, from the three chains' values
under g. -/
theorem opened_wholeA (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a' b').det g =
      some e')
    (hshape : shapesFit a W = true) (hseal : sealBare W = true) (hsalts : saltsFit sb W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32) (hcfg : cfg.size = 32)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₁ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₁ (glue a' b' e').1)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₂ ((chainsOf C (WholeD.of a W) tF tJ t3).rho₂ (glue a' b' e').1)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT C (WholeD.of a W).ds₃
        ((chainsOf C (WholeD.of a W) tF tJ t3).rho₃ (glue a' b' e').1))) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (chainsOf C (WholeD.of a W) tF tJ t3).sh
        (chainsOf C (WholeD.of a W) tF tJ t3).ann
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh (glue a' b' e').2.1
        (readS (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π (glue a' b' e').1
          (glue a' b' e').2.1) π.opens ∧
      OpenedE (256 + 8 * sb) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).maxDepth
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext
        (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1) π.ext := by
  obtain ⟨o1, o2, o3, oE⟩ := opened_atA C K chal a W tF tJ t3 silent run g sb cfg pF pJ p3 salt path
    r π h x a' b' e' h₁ h₂ h₃ hshape hseal hsalts hrun hcfg hl₁ hl₂ hl₃ hd₁ hd₂ hd₃
  exact ⟨opened_three _ _ _ x π a' b' e' o1 o2 o3, oE⟩

end File

end OnBytes.Maker
