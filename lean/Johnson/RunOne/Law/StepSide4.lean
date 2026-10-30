-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/StepSide4.lean: THE STATE's
SIDE OF THE TABLES' PROMISE ON THE KEY FILE's FIRST CHAIN, ACROSS FOUR BLOCKS: at the yes of the
kind K3's own block of a lookup (borders 4 → 5 and 10 → 11) and of the layer behind it (5 → 6 and
11 → 12): the state's side at the border in front gives the state's side at the border behind. ON
THE STATE ALONE: no strings, no witness, no reading.

Main names:
  StepInv (Johnson/Top/Fire/Code/ReachedInv.lean), ASide (Johnson/RunOne/KeyASide.lean): THOSE
    FILES' OWN: at every yes of b on rounds that fit: I in front gives I' behind; the state's side
    at border k.
  JSide one set k: WHAT MORE OF THE STATE THE LAYER's STEP WANTS IN FRONT: at the borders 5 and 11:
    the state holds what the kind's own block has left (HeardOk: a ledger and a hearing; the
    ledger sized, its count behind the lookup's hidden values; as many heard claims on keys as the
    lookup has parts, of the parts' sizes); at every other border: nothing.
  step_4 | step_10 | step_5 | step_11: StepInv at (ASide ∧ JSide).
  k3_d | layer_d: THE LIGHTER ONES: a yes of either block leaves s.d (the statement, the book of
    trees, the count of roots) as it is: no premise.

Premises of the four: the plan's ranges are admitted (Wf.admitted); the lookup is there.

Object: the bare blocks at the places 4, 5, 10, 11 of Key.firstChain's blocksInOrder list. User: the fold of
the state's side along a history.
Limits. Nothing on the claims. Nothing on soundness.

-/
import Johnson.RunOne.Law.LayerBehind
import Johnson.RunOne.Law.Walk
import Johnson.RunOne.KeyASide
import Johnson.Top.Fire.Code.ReachedInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.StepSide4
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Where lookupSeat pinned sentB groupB doneB core₁
  shape₁ shape₁_iff layer caller lookupPlace Placed MaskWith)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ ties₁ tiesA sizesB open₁ ASide)
open LPFD (StepInv)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.TieBehind
open Johnson.RunOne.Law.TieBehindK3
open Johnson.RunOne.Law.LayerBehind

/-- Lookup number l, as the first chain's link takes it. -/
abbrev lk (one : OneTime) (l : ℕ) : VerifiableInference.Desc.Key.Lookup :=
  Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) (Lof one l)

/-- What more of the state the layer's step wants in front. -/
def JSide (one : OneTime) (set : Setting) (k : ℕ) (s : FirstState) : Prop :=
  if k = 5 then HeardOk lookupSeat (lookupPlace set 0 (lk one 0)) s
  else if k = 11 then HeardOk lookupSeat (lookupPlace set 1 (lk one 1)) s
  else True

theorem jside_5 (one : OneTime) (set : Setting) (s : FirstState) :
    JSide one set 5 s = HeardOk lookupSeat (lookupPlace set 0 (lk one 0)) s := if_pos rfl

theorem jside_11 (one : OneTime) (set : Setting) (s : FirstState) :
    JSide one set 11 s = HeardOk lookupSeat (lookupPlace set 1 (lk one 1)) s := by
  unfold JSide
  rw [if_neg (by decide), if_pos rfl]

theorem jside_else (one : OneTime) (set : Setting) (k : ℕ) (h5 : k ≠ 5) (h11 : k ≠ 11)
    (s : FirstState) : JSide one set k s := by
  unfold JSide
  rw [if_neg h5, if_neg h11]
  trivial

/-! ## The lighter ones -/

/-- The link's three runs of claims leave s.d. -/
theorem claims_d {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {cls : List Claim}
    (h : claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")] s = .ok (cls, s')) : s'.d = s.d := by
  unfold claimsIn claimsInBy at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  obtain ⟨x2, h, h3⟩ := bindB h
  obtain ⟨x1, h, h2⟩ := bindB h
  obtain ⟨x0, h0, h1⟩ := bindB h
  cases h0
  obtain ⟨z1, r1, rfl⟩ := runIn_ok (o := (1, "objects")) rfl h1
  obtain ⟨z2, r2, rfl⟩ := runIn_ok (o := (1, "planes")) rfl h2
  obtain ⟨z3, r3, e3⟩ := runIn_ok (o := (1, "guests")) rfl h3
  obtain ⟨F1, a1, r1⟩ := bindX r1
  obtain ⟨g1, a2, r1⟩ := bindX r1
  cases r1
  obtain ⟨F2, b1, r2⟩ := bindX r2
  obtain ⟨g2, b2, r2⟩ := bindX r2
  obtain ⟨_, -, r2⟩ := bindX r2
  obtain ⟨y, b4, r2⟩ := bindX r2
  obtain ⟨l, b5, r2⟩ := bindX r2
  cases r2
  have h9 := namedX r3
  cases h9
  obtain ⟨-, rfl⟩ := Prod.mk.inj e3
  rfl

/-- **A yes of the kind's own block leaves s.d.** -/
theorem k3_d {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (lookupKind lookupSeat before bits [] p : Block FirstState Claim).decide s rs gs = .ok s') :
    s'.d = s.d := by
  obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ h
  rfl

/-- **A yes of the layer leaves s.d.** -/
theorem layer_d {one : OneTime} {set : Setting} {i : ℕ} {x : VerifiableInference.Desc.Key.Lookup}
    {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG} {s s' : FirstState}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (layer one set i x (claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")])).decide s rs gs = .ok s') : s'.d = s.d := by
  obtain ⟨cls, s1, F, g', rows, keys, e1, -, -, -, -, rfl⟩ := layerD_law h
  show s1.d = s.d
  exact claims_d e1

/-! ## The four steps -/

variable (one : OneTime) (set : Setting) (at_ : Where) (s : FirstState)

/-- Where s.d stays and the pins are the same, the state's side goes with the book-keeping's
step. -/
theorem aside_of_d (k k' : ℕ) (s s' : FirstState) (hd : s'.d = s.d)
    (hpin : pinned (open₁ 2 k') = pinned (open₁ 2 k))
    (hk : 2 ≤ k' ∧ k' ≤ 15 → 2 ≤ k ∧ k ≤ 15)
    (hsh : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k s = true →
      shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k' s' = true)
    (h : ASide one at_ k s) : ASide one at_ k' s' :=
  ⟨hsh h.1, by rw [hd, hpin]; exact h.2.1, by rw [hd]; exact h.2.2.1,
    fun hb => by rw [hd]; exact h.2.2.2 (hk hb)⟩

/-- The ledger in front of the kind's own block of lookup 0 has its sizes: off the
book-keeping. -/
theorem sized_4 (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 s = true)
    (F0 : Fork) (hF : s.base.fork = some F0) : PscRun.Sized F0 := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) &&
      (!s.base.heard.isSome && s.base.home.size == slots₁ one 0 && _)) = true := h
  have h4 : ((s.base.fork.map _).any _) = true :=
    (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').2).2
  rw [hF] at h4
  have h5 : (F0.next == 0 && F0.ns == slots₁ one 0 &&
      (F0.vp.size == F0.ns && F0.mf.size == F0.ns && F0.gotF.size == F0.ns) && _) = true := h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  exact ⟨h5.1.2.1.1, h5.1.2.1.2, h5.1.2.2⟩

/-- **THE STATE's SIDE ACROSS THE KIND's OWN BLOCK OF LOOKUP 0**: border 4 → 5. -/
theorem step_4 (hW : Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true)
    (hl : 0 < one.ranges.lookups.length) :
    StepInv (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set 0 (lk one 0)))
      (fun s => ASide one at_ 4 s ∧ JSide one set 4 s)
      (fun s => ASide one at_ 5 s ∧ JSide one set 5 s) := by
  intro s s' rs gs _ hy hA
  have hadm := Lk6.adm_of_tests one.ranges.messageId (Wf.matrixOf one.lin) _
    (tests_at hW hl).2.1 (tests_at hW hl).2.2
  have hS : ∀ F0, lookupSeat.fork s = some F0 → PscRun.Sized F0 := fun F0 hF =>
    sized_4 one s ((shape₁_iff _ _ _ _ _ _ _).1 hA.1.1).2 F0 hF
  have hh : HomeIs (lookupPlace set 0 (lk one 0)).face
      (lookupPlace set 0 (lk one 0)).first (fun _ => default) (fun _ => default)
      (fun j => (homes (faceOfLkp (lk one 0))
        ((List.range (faceOfLkp (lk one 0)).slots).map fun _ => default)
        ((List.range (faceOfLkp (lk one 0)).slots).map fun _ => default)).getD j default) :=
    fun j _ => by rw [show (lookupPlace set 0 (lk one 0)).first + j = j from Nat.zero_add j]; rfl
  have hf := faceIsK Unit one.ranges.messageId (Wf.matrixOf one.lin) (Lof one 0) [] () hadm
    (d_le (tests_at hW hl).2.1)
  obtain ⟨g, G, e2, g1, g2, g3⟩ :=
    yes_ledger (σ := lookupSeat) [(1, 0), (1, 1)] 0 [] hf hadm hh hS hy
  obtain ⟨hH, -⟩ := heardOk_of_yes (σ := lookupSeat) [(1, 0), (1, 1)] 0 [] hf hadm hh
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hS hy
  subst e2
  have g1' : G.next = slots₁ one 0 := by
    rw [slots₁_eq _ 0 hl, g1]
    exact Nat.zero_add _
  have g2' : G.ns = slots₁ one 0 := by
    rw [slots₁_eq _ 0 hl, g2]
    rfl
  exact ⟨aside_of_d one at_ 4 5 s _ rfl rfl (by omega) (sh_4_5 one s g G g1' g2' g3) hA.1,
    by rw [jside_5]; exact hH⟩

/-- The ledger in front of the kind's own block of lookup 1 has its sizes: off the
book-keeping. -/
theorem sized_10 (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 s = true)
    (F0 : Fork) (hF : s.base.fork = some F0) : PscRun.Sized F0 := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) &&
      (!s.base.heard.isSome && s.base.home.size == slots₁ one 1 && _)) = true := h
  have h4 : ((s.base.fork.map _).any _) = true :=
    (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').2).2
  rw [hF] at h4
  have h5 : (F0.next == 0 && F0.ns == slots₁ one 1 &&
      (F0.vp.size == F0.ns && F0.mf.size == F0.ns && F0.gotF.size == F0.ns) && _) = true := h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  exact ⟨h5.1.2.1.1, h5.1.2.1.2, h5.1.2.2⟩

/-- **THE STATE's SIDE ACROSS THE KIND's OWN BLOCK OF LOOKUP 1**: border 10 → 11. -/
theorem step_10 (hW : Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true)
    (hl : 1 < one.ranges.lookups.length) :
    StepInv (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set 1 (lk one 1)))
      (fun s => ASide one at_ 10 s ∧ JSide one set 10 s)
      (fun s => ASide one at_ 11 s ∧ JSide one set 11 s) := by
  intro s s' rs gs _ hy hA
  have hadm := Lk6.adm_of_tests one.ranges.messageId (Wf.matrixOf one.lin) _
    (tests_at hW hl).2.1 (tests_at hW hl).2.2
  have hS : ∀ F0, lookupSeat.fork s = some F0 → PscRun.Sized F0 := fun F0 hF =>
    sized_10 one s ((shape₁_iff _ _ _ _ _ _ _).1 hA.1.1).2 F0 hF
  have hh : HomeIs (lookupPlace set 1 (lk one 1)).face
      (lookupPlace set 1 (lk one 1)).first (fun _ => default) (fun _ => default)
      (fun j => (homes (faceOfLkp (lk one 1))
        ((List.range (faceOfLkp (lk one 1)).slots).map fun _ => default)
        ((List.range (faceOfLkp (lk one 1)).slots).map fun _ => default)).getD j default) :=
    fun j _ => by rw [show (lookupPlace set 1 (lk one 1)).first + j = j from Nat.zero_add j]; rfl
  have hf := faceIsK Unit one.ranges.messageId (Wf.matrixOf one.lin) (Lof one 1) [] () hadm
    (d_le (tests_at hW hl).2.1)
  obtain ⟨g, G, e2, g1, g2, g3⟩ :=
    yes_ledger (σ := lookupSeat) [(1, 0), (1, 1)] 0 [] hf hadm hh hS hy
  obtain ⟨hH, -⟩ := heardOk_of_yes (σ := lookupSeat) [(1, 0), (1, 1)] 0 [] hf hadm hh
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hS hy
  subst e2
  have g1' : G.next = slots₁ one 1 := by
    rw [slots₁_eq _ 1 hl, g1]
    exact Nat.zero_add _
  have g2' : G.ns = slots₁ one 1 := by
    rw [slots₁_eq _ 1 hl, g2]
    rfl
  exact ⟨aside_of_d one at_ 10 11 s _ rfl rfl (by omega) (sh_10_11 one s g G g1' g2' g3) hA.1,
    by rw [jside_11]; exact hH⟩

/-- In front of the layer of lookup 0 just 0 lookups have laid: off the ties. -/
theorem lens_5 (h : ties₁ one 5 s = true) :
    s.base.rows.length = 0 ∧ s.base.keys.length = 0 := by
  have h' : (tiesA one 5 s &&
      (s.base.rows.length == 0 && s.base.keys.length == 0 && _ && _ && _ && _) &&
      sizesB one 5 s) = true := h
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1.1.1.1.1, h2.1.1.1.1.2⟩

/-- **THE STATE's SIDE ACROSS THE LAYER OF LOOKUP 0**: border 5 → 6. -/
theorem step_5 (hW : Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true)
    (hl : 0 < one.ranges.lookups.length) :
    StepInv (layer one set 0 (lk one 0)
        (claimsIn [caller one 0 (lk one 0),
          lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set 0 (lk one 0))]
          [(1, "objects"), (1, "planes"), (1, "guests")]))
      (fun s => ASide one at_ 5 s ∧ JSide one set 5 s)
      (fun s => ASide one at_ 6 s ∧ JSide one set 6 s) := by
  intro s s' rs gs _ hy hA
  have hH := hA.2
  rw [jside_5] at hH
  obtain ⟨G, F', rows, keys, hG, e2, g1, g2, g3, g4, g5, g6⟩ := yes_layer hH hy
  subst e2
  obtain ⟨hr, hk⟩ := lens_5 one s ((shape₁_iff _ _ _ _ _ _ _).1 hA.1.1).1
  have hlen : keys.length = (Lof one 0).parts.length := by
    rw [g6]
    exact List.length_map _
  exact ⟨aside_of_d one at_ 5 6 s _ rfl rfl (by omega)
    (sh_5_6 one s F' rows keys G hG g1 g2 g3 g4
      (done_step one s F' rows keys 0 (Lof one 0) (tests_at hW hl).1 hr hk g5 hlen)) hA.1,
    jside_else one set 6 (by decide) (by decide) _⟩

/-- In front of the layer of lookup 1 just 1 lookups have laid: off the ties. -/
theorem lens_11 (h : ties₁ one 11 s = true) :
    s.base.rows.length = 1 ∧ s.base.keys.length = 1 := by
  have h' : (tiesA one 11 s &&
      (s.base.rows.length == 1 && s.base.keys.length == 1 && _ && _ && _ && _) &&
      sizesB one 11 s) = true := h
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1.1.1.1.1, h2.1.1.1.1.2⟩

/-- **THE STATE's SIDE ACROSS THE LAYER OF LOOKUP 1**: border 11 → 12. -/
theorem step_11 (hW : Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true)
    (hl : 1 < one.ranges.lookups.length) :
    StepInv (layer one set 1 (lk one 1)
        (claimsIn [caller one 1 (lk one 1),
          lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set 1 (lk one 1))]
          [(1, "objects"), (1, "planes"), (1, "guests")]))
      (fun s => ASide one at_ 11 s ∧ JSide one set 11 s)
      (fun s => ASide one at_ 12 s ∧ JSide one set 12 s) := by
  intro s s' rs gs _ hy hA
  have hH := hA.2
  rw [jside_11] at hH
  obtain ⟨G, F', rows, keys, hG, e2, g1, g2, g3, g4, g5, g6⟩ := yes_layer hH hy
  subst e2
  obtain ⟨hr, hk⟩ := lens_11 one s ((shape₁_iff _ _ _ _ _ _ _).1 hA.1.1).1
  have hlen : keys.length = (Lof one 1).parts.length := by
    rw [g6]
    exact List.length_map _
  exact ⟨aside_of_d one at_ 11 12 s _ rfl rfl (by omega)
    (sh_11_12 one s F' rows keys G hG g1 g2 g3 g4
      (done_step one s F' rows keys 1 (Lof one 1) (tests_at hW hl).1 hr hk g5 hlen)) hA.1,
    jside_else one set 12 (by decide) (by decide) _⟩

end Johnson.RunOne.Law.StepSide4

#print axioms Johnson.RunOne.Law.StepSide4.jside_5
#print axioms Johnson.RunOne.Law.StepSide4.jside_11
#print axioms Johnson.RunOne.Law.StepSide4.jside_else
#print axioms Johnson.RunOne.Law.StepSide4.claims_d
#print axioms Johnson.RunOne.Law.StepSide4.k3_d
#print axioms Johnson.RunOne.Law.StepSide4.layer_d
#print axioms Johnson.RunOne.Law.StepSide4.aside_of_d
#print axioms Johnson.RunOne.Law.StepSide4.sized_4
#print axioms Johnson.RunOne.Law.StepSide4.sized_10
#print axioms Johnson.RunOne.Law.StepSide4.lens_5
#print axioms Johnson.RunOne.Law.StepSide4.lens_11
#print axioms Johnson.RunOne.Law.StepSide4.step_4
#print axioms Johnson.RunOne.Law.StepSide4.step_10
#print axioms Johnson.RunOne.Law.StepSide4.step_5
#print axioms Johnson.RunOne.Law.StepSide4.step_11
