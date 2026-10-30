-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/ClaimJoin.lean: the code switch: THE CARRIED CLAIM's ROW, as the
program lays it (switchCarried; RowsOrder.lean's carriedOf), is the old claim's vector, written out
as a function of the old single rows (vecOf), carried along the map of names iJ.

  vecOf   THE OLD CLAIM's VECTOR ON THE FOLDED COMPLEX WITH KEPT SLOTS, a function of the record's
          single rows and of the slots' names:
            entry j of the folded main row:  the form old.c at j
            entry j of the kept slot κ:  THE SUM, over the claim's kept forms that name κ's member,
              of the form's entry at row κ + 2 ^ rowBits * j
            entry j of the carried mask row:  old.d's vector number 0 at j
            entry j of the fresh mask row:  old.d's vector number 1 at j
  oldVec  one kept form's share of it
  ClaimOK  what is asked of the old claim: the main form's tensors have the main code's index bits;
          the two written-out vectors are no longer than the mask code's message; each kept form's
          place, found by the program's own search, has the form's old number, is a member a of the
          frame with its slots (Slots), and a slot κ is that member's just if its place has the
          member's old number ((pl κ).old = p.2.old ↔ mem κ = a); there are as many places as kept
          forms (long)
  addKept_add, kept_fold, lift_form, mask_term, stretchAt_more, pushTo_add, pushTo_four, oldVec_eq,
    map_zip_fst, kept_sum
          steps
  claim_reads  THE JOIN: ReadsAs … (carriedOf W old ks) (pushTo iJ (vecOf …))
The target: carriedOf's target is old.target by definition.
LIMITS. FrameOK, Names, NamesK, Slots and ClaimOK are PREMISES (brought further, not paid: Paid.lean
makes them from the record AtSwitch and four plain clauses, all premises). ReadsAs speaks of the
entries of the new sending alone. old.masks = 2 is a premise; so are h0 and h1: the two mask places
aM0 and aM1 are the frame's own (maskAt 0 and 1). No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.KeptFormJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

/-! ## Steps -/

theorem pushTo_add {I Ent : Type} [Fintype I] (p : I → Ent) (c c' : I → GE) (n : Ent) :
    pushTo p (fun i => c i + c' i) n = pushTo p c n + pushTo p c' n := by
  unfold pushTo
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p i = n
  · simp [h]
  · simp [h]

theorem pushTo_four {K A B Ent : Type} [Fintype K] [Fintype A] [Fintype B]
    (p : (Option K × A) ⊕ (B ⊕ B) → Ent) (c : (Option K × A) ⊕ (B ⊕ B) → GE) (n : Ent) :
    pushTo p c n =
      pushTo (fun a => p (.inl (none, a))) (fun a => c (.inl (none, a))) n +
        (∑ κ, pushTo (fun a => p (.inl (some κ, a))) (fun a => c (.inl (some κ, a))) n) +
        (pushTo (fun b => p (.inr (.inl b))) (fun b => c (.inr (.inl b))) n +
          pushTo (fun b => p (.inr (.inr b))) (fun b => c (.inr (.inr b))) n) := by
  unfold pushTo
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_sum_type]

/-- A form carried over adds to a row what it gives on the row without parts. -/
theorem addKept_add (W : SwitchFrame) (r : OnBytes.Row) (k : KeptPlace) (c : Form) (o : ℕ)
    (part : Part) (J : ℕ) :
    coefAt (W.addKept r k c) o part J = coefAt r o part J + coefAt (W.addKept {} k c) o part J := by
  unfold SwitchFrame.addKept
  rw [coefAt_addKept, coefAt_addKept, coefAt_empty, zero_add, add_assoc]

/-- A stretch whose coefficients are 0 from n on may be taken longer. -/
theorem stretchAt_more (places : SwitchPlaces) (first n m : ℕ) (h : n ≤ m) (c : ℕ → GE)
    (h0 : ∀ i, n ≤ i → c i = 0) (J : ℕ) :
    stretchAt places first n c J = stretchAt places first m c J := by
  unfold stretchAt
  refine Finset.sum_subset (fun i hi => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hi) h)) fun i _ hi => ?_
  rw [h0 i (Nat.le_of_not_lt fun k => hi (Finset.mem_range.2 k))]
  simp

/-- A lifted form, at an index of g's main table, as a sum over the message's entries. -/
theorem lift_form (W : SwitchFrame) {aMain aM0 aT0 aM1 aT1 : ℕ}
    (F : FrameOK W aMain aM0 aT0 aM1 aT1) (c : Form)
    (hc : ∀ v ∈ c.tensors, v.vars = W.code.logEll) (C : Fmt.M1.Code) (hC : C = codeOf W.code)
    (J : ℕ) (hJ : J < 2 ^ W.tableBits) :
    formAt (switchLift c W.code.logEll W.mainCut W.rowBits W.tableBits) J =
      ∑ j : Fin C.l, if cutIndex W.mainCut W.rowBits j.val = J then formAt c j.val else 0 := by
  subst hC
  have hl : (codeOf W.code).l = 2 ^ W.code.logEll := F.pow
  by_cases ex : ∃ j, j < 2 ^ W.code.logEll ∧ cutIndex W.mainCut W.rowBits j = J
  · obtain ⟨j0, hj0, rfl⟩ := ex
    rw [formAt_switchLift_cutIndex c _ _ _ _ hc F.cutBits F.cutRow F.cutTab F.cutAl F.cutFirst j0
      hj0, Finset.sum_eq_single (⟨j0, by rw [hl]; exact hj0⟩ : Fin (codeOf W.code).l)]
    · simp
    · intro j _ hne
      rw [if_neg]
      intro e
      exact hne (Fin.ext (cutIndex_inj _ _ F.cutRow F.cutAl F.cutFirst e))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [formAt_switchLift_off c _ _ _ _ hc F.cutBits F.cutRow F.cutTab F.cutAl F.cutFirst J hJ
      fun j hj e => ex ⟨j, hj, e⟩]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg]
    intro e
    exact ex ⟨j.val, lt_of_lt_of_eq j.isLt hl, e⟩

/-! ## The old claim's vector -/

section Vec
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K]

/-- One kept form's share: the form c on the old main table of the member whose number is o. -/
noncomputable def oldVec (row : K → ℕ) (pl : K → KeptPlace) (o : ℕ) (c : Form) :
    (s.cKept K).J → GE
  | .inl (some κ, j) =>
    if (pl κ).old = o then formAt c (row κ + 2 ^ (pl κ).rowBits * j.val) else 0
  | _ => 0

/-- **The old claim's vector.** -/
noncomputable def vecOf (old : SingleRows) (row : K → ℕ) (pl : K → KeptPlace) : (s.cKept K).J → GE
  | .inl (none, j) => formAt old.c j.val
  | .inl (some κ, j) =>
    (old.kept.toList.map fun f => oldVec s K row pl f.oracle f.c (.inl (some κ, j))).sum
  | .inr (.inl j) => readV (old.d.getD 0 #[]) j.val
  | .inr (.inr j) => readV (old.d.getD 1 #[]) j.val

end Vec

section Join
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] (cs : Codes) (l : List (OracleShape × ℕ))

/-- What is asked of the old claim. ks: the places that the program's search finds for the kept
forms. -/
structure ClaimOK (W : SwitchFrame) (ids : ℕ → ℕ) (mem row : K → ℕ) (pl : K → KeptPlace)
    (old : SingleRows) (ks : List KeptPlace) : Prop where
  mainVars : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll
  d0 : (old.d.getD 0 #[]).size ≤ W.zk.ell
  d1 : (old.d.getD 1 #[]).size ≤ W.zk.ell
  forms : ∀ p ∈ old.kept.toList.zip ks, p.2.old = p.1.oracle ∧
    ∃ a, W.kept[a]? = some p.2 ∧ Slots s K cs l W ids mem row a p.2 ∧
      ∀ κ, (pl κ).old = p.2.old ↔ mem κ = a
  long : ks.length = old.kept.toList.length

end Join

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}

/-- One kept form's share is slotVec at its member's number. -/
theorem oldVec_eq (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) {a : ℕ} {k : KeptPlace}
    (hk : W.kept[a]? = some k) (same : ∀ κ, (pl κ).old = k.old ↔ mem κ = a) (c : Form) :
    oldVec s K row pl k.old c = slotVec s K mem row a k.rowBits c := by
  funext x
  rcases x with ⟨_ | κ, j⟩ | x
  · rfl
  · show (if (pl κ).old = k.old then formAt c (row κ + 2 ^ (pl κ).rowBits * j.val) else 0) =
      if mem κ = a then formAt c (row κ + 2 ^ k.rowBits * j.val) else 0
    by_cases hm : mem κ = a
    · have hp : pl κ = k := by
        have h := member κ
        rw [hm, hk] at h
        exact (Option.some.inj h).symm
      rw [if_pos hm, if_pos ((same κ).2 hm), hp]
    · rw [if_neg hm, if_neg fun e => hm ((same κ).1 e)]
  · rfl

/-- The loop over the kept forms. -/
theorem kept_fold (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) :
    ∀ (L : List (KeptForm × KeptPlace)),
      (∀ p ∈ L, p.2.old = p.1.oracle ∧ ∃ a, W.kept[a]? = some p.2 ∧
        Slots s K cs l W ids mem row a p.2 ∧ ∀ κ, (pl κ).old = p.2.old ↔ mem κ = a) →
      ∀ (r : OnBytes.Row) (n : (sigOf cs l).Ent),
        coefAt (L.foldl (fun (r : OnBytes.Row) p => W.addKept r p.2 p.1.c) r)
            (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
          coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 +
            (L.map fun p => pushTo iJ (oldVec s K row pl p.1.oracle p.1.c) n).sum
  | [], _, r, n => by simp
  | p :: L, h, r, n => by
    obtain ⟨ho, a, hk, Sl, same⟩ := h p (List.mem_cons_self ..)
    rw [List.foldl_cons, kept_fold D DK member L (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      addKept_add, List.map_cons, List.sum_cons, keptForm_reads D DK member a p.2 hk Sl p.1.c n,
      ← ho, oldVec_eq member hk same, add_assoc]

theorem map_zip_fst {α β γ : Type} (g : α → γ) : ∀ (l₁ : List α) (l₂ : List β),
    l₁.length ≤ l₂.length → (l₁.zip l₂).map (fun p => g p.1) = l₁.map g
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_zip_fst g l₁ l₂ (Nat.le_of_succ_le_succ h)]

/-- The kept forms' shares, slot by slot. -/
theorem kept_sum (iJ : (s.cKept K).J → (sigOf cs l).Ent) (row : K → ℕ) (pl : K → KeptPlace)
    (n : (sigOf cs l).Ent) : ∀ Lf : List KeptForm,
    (Lf.map fun f => pushTo iJ (oldVec s K row pl f.oracle f.c) n).sum =
      ∑ κ, pushTo (fun j : Fin s.C.l => iJ (.inl (some κ, j)))
        (fun j => (Lf.map fun f => oldVec s K row pl f.oracle f.c (.inl (some κ, j))).sum) n
  | [] => by simp [pushTo]
  | f :: Lf => by
    rw [List.map_cons, List.sum_cons, kept_sum iJ row pl n Lf,
      pushTo_slots (K := K) (A := Fin s.C.l) (B := Fin s.Z.l ⊕ Fin s.Z.l) iJ
        (oldVec s K row pl f.oracle f.c) (fun _ => rfl) (fun _ => rfl) n,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [← pushTo_add]
    simp only [List.map_cons, List.sum_cons]

/-- A written-out vector on a mask row's message. -/
theorem mask_term (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (j aM aT : ℕ)
    (hM : MaskAt W j aM aT) (pM : Fin s.Z.l → (sigOf cs l).Ent)
    (hpM : ∀ i, entAt cs l (pM i) = (0, W.restPart,
        W.places.get (aM + i.val))) (d : Array OnBytes.E)
    (hd : d.size ≤ W.zk.ell) (r : OnBytes.Row) (n : (sigOf cs l).Ent) :
    coefAt (switchAddRestE r W.g W.restPart (switchPieces W.places aM d.size) d)
        (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
      coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 +
        pushTo pM (fun i => readV d i.val) n := by
  have hl : W.zk.ell = s.Z.l := by rw [D.codeZ]; rfl
  rw [coefAt_restE_at _ _ _ _ _ _ (fun i k h1 h2 => hM.incM i k h1 (lt_of_lt_of_le h2 hd)),
    pushTo_at cs l _ _ 0 W.restPart _ hpM n]
  refine congrArg _ (if_ctx_congr (tab_rest (D.gIs n)) (fun _ => ?_) fun _ => rfl)
  rw [stretchAt_more _ _ _ _ hd _ (fun i hi => readV_of_le d i hi), hl]
  unfold stretchAt
  exact Finset.sum_range _

/-- **The carried claim's row.** -/
theorem claim_reads (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (old : SingleRows) (ks : List KeptPlace)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ClaimOK s K cs l W ids mem row pl old ks) :
    ReadsAs cs l ids (carriedOf W old ks) (pushTo iJ (vecOf s K old row pl)) := by
  intro n
  show coefAt ((List.range old.masks).foldl
      (fun (r : OnBytes.Row) j =>
        switchAddRestE r W.g W.restPart
          (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j #[]).size)
          (old.d.getD j #[]))
      ((old.kept.toList.zip ks).foldl (fun (r : OnBytes.Row) p => W.addKept r p.2 p.1.c)
        (({} : OnBytes.Row).addForm W.g
          (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits)))) _ _ _ = _
  have split := pushTo_four (K := K) (A := Fin s.C.l) (B := Fin s.Z.l) iJ (vecOf s K old row pl) n
  rw [hm, show List.range 2 = [0, 1] from rfl, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    ← h0, ← h1,
    mask_term D 1 aM1 aT1 F.mask1 _ D.mask1Msg _ Q.d1,
        mask_term D 0 aM0 aT0 F.mask0 _ D.mask0Msg _ Q.d0,
    kept_fold D DK member _ Q.forms, coefAt_addForm, coefAt_empty, zero_add, split, add_assoc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) rfl
  · show _ = pushTo (fun j : Fin s.C.l => iJ (.inl (none, j))) (fun j => formAt old.c j.val) n
    rw [pushTo_at cs l _ _ 0 Part.main _ D.mainMsg n]
    exact if_ctx_congr (tab_main (D.gIs n))
      (fun c => lift_form W F old.c Q.mainVars s.C D.codeC _ (D.mainIn n c.1 c.2)) fun _ => rfl
  · rw [map_zip_fst (fun f : KeptForm => pushTo iJ (oldVec s K row pl f.oracle f.c) n) _ _
      (le_of_eq Q.long.symm)]
    exact kept_sum iJ row pl n _

end Join

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.claim_reads
