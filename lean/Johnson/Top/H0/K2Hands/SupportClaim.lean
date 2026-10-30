-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SupportClaim.lean: the code switch: THE CARRIED CLAIM's ROW AND THE
OLD SAMPLE ROWS HAVE NO COEFFICIENT OUTSIDE THE ENTRIES OF THE NEW SENDING, as far as that can be
said of forms that are the record's.

Support.lean has this for the generator rows. Here the two other sorts of rows. Both are made of
forms on a kept member's old main table, carried over by the program's addKept, and (the claim) of
the main form and of two written-out vectors.
  keptForm_only   a form carried over
  sample_only     an old sample row
  kept_fold_at, list_sum_ne, slot_entry  steps
  InClaim         the indices of which the statement speaks: in g's main table those below 2 ^
                  tableBits; IN A KEPT MEMBER's NEW MAIN TABLE THOSE THAT NAME A ROW OF THE MEMBER
                  AND A PLACE OF THE ROW; in every other table all
  claim_only      the carried claim's row
WHAT STAYS UNSAID, AND WHY. In a kept member's new main table an index can name no entry: its row
number (index mod 2 ^ rowBits) is not below the member's rows, or its place is not below the code's
message length. The form there is the record's own (a claim's kept form; a stored sample row):
nothing in the switch makes it 0 at such an index, and addKept carries it over as it stands. So the
statement is silent there. Whether that is harmless hangs on what "the row holds" means on the
text's side: if a table is read as 0 at the rows that nobody sent (as the comment above
ioppLastRows, OnBytes/Iop/Prox.lean, says of a group's second row: "a row of zeros that nobody
sent"), such a coefficient meets a 0. That is a reading, not a lemma of this file.
LIMITS. FrameOK, Names, NamesK, Slots and ClaimOK are premises (brought further, not paid: Paid.lean
makes them from the record AtSwitch and four plain clauses, all premises). No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.Support
import Johnson.Top.H0.K2Hands.ClaimJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

theorem list_sum_ne {α : Type} (f : α → GE) : ∀ l : List α, (l.map f).sum ≠ 0 → ∃ x ∈ l, f x ≠ 0
  | [], h => absurd rfl h
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons] at h
    rcases add_ne h with k | k
    · exact ⟨a, List.mem_cons_self .., k⟩
    · obtain ⟨x, hx, hf⟩ := list_sum_ne f l k
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

/-- The loop over the kept forms, at any three numbers. -/
theorem kept_fold_at (W : SwitchFrame) (o : ℕ) (part : Part) (J : ℕ) :
    ∀ (L : List (KeptForm × KeptPlace)) (r : OnBytes.Row),
      coefAt (L.foldl (fun (r : OnBytes.Row) p => W.addKept r p.2 p.1.c) r) o part J =
        coefAt r o part J + (L.map fun p => coefAt (W.addKept {} p.2 p.1.c) o part J).sum
  | [], r => by simp
  | p :: L, r => by
    rw [List.foldl_cons, kept_fold_at W o part J L, addKept_add, List.map_cons, List.sum_cons,
      add_assoc]

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}

/-- The entry of a kept member's table at an index that names a row and a place. -/
theorem slot_entry (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) {a : ℕ} {k : KeptPlace}
    (hk : W.kept[a]? = some k) (Sl : Slots s K cs l W ids mem row a k) (X : ℕ)
    (h1 : X % 2 ^ k.rowBits < k.rows) (h2 : X / 2 ^ k.rowBits < s.C.l) :
    ∃ n : (sigOf cs l).Ent, entAt cs l n = keptNm W a k X := by
  obtain ⟨κ, ⟨m0, r0⟩, -⟩ := Sl.one _ h1
  have hp : pl κ = k := by
    have h := member κ
    rw [m0, hk] at h
    exact (Option.some.inj h).symm
  refine ⟨iJ (.inl (some κ, ⟨_, h2⟩)), ?_⟩
  rw [DK.keptMsg κ ⟨_, h2⟩, m0, hp, r0]
  unfold keptAt
  rw [Nat.mod_add_div]

/-- **A form on a kept member's old main table, carried over.** -/
theorem keptForm_only (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (a : ℕ) (k : KeptPlace)
    (hk : W.kept[a]? = some k) (Sl : Slots s K cs l W ids mem row a k) (c : Form) :
    OnlyAt cs l ids
      (fun o part J => o = k.anew → part = Part.main →
        J % 2 ^ k.rowBits < k.rows ∧ J / 2 ^ k.rowBits < s.C.l)
      (W.addKept {} k c) := by
  intro o part J hin hne
  have hne' : coefAt (switchAddKept {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c) o part J
      ≠ 0 := hne
  by_cases cA : o = k.anew ∧ part = Part.main
  · obtain ⟨rfl, rfl⟩ := cA
    rw [addKept_new {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c Sl.notG Sl.nodup,
      coefAt_empty, zero_add] at hne'
    by_cases hp : J ∈ k.pad.map (·.index)
    · rw [if_pos hp] at hne'
      exact absurd rfl hne'
    · obtain ⟨h1, h2⟩ := hin rfl rfl
      obtain ⟨n, hn⟩ := slot_entry DK member hk Sl J h1 h2
      unfold keptNm at hn
      rw [if_neg hp] at hn
      exact ⟨n, (Sl.anewIs n).2 (by rw [hn]), by rw [hn], by rw [hn]⟩
  · by_cases cB : o = W.g ∧ part = W.restPart
    · obtain ⟨rfl, rfl⟩ := cB
      rw [addKept_g {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c Sl.notG, coefAt_empty,
        zero_add] at hne'
      obtain ⟨q, hq, e, -⟩ := stretchAt_ne hne'
      obtain ⟨n, hn⟩ := slot_entry DK member hk Sl _ (Sl.pad q hq).1 (Sl.pad q hq).2
      have hm : (k.pad.getD q default).index ∈ k.pad.map (·.index) := by
        rw [List.getD_eq_getElem _ _ hq]
        exact List.mem_map_of_mem (List.getElem_mem hq)
      unfold keptNm restAt at hn
      rw [if_pos hm, padNoOf_at _ Sl.nodup q hq, e] at hn
      exact named_g D n hn
    · exact absurd ((addKept_other {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c o part cA cB
        J).trans (coefAt_empty _ _ _)) hne'

/-- **An old sample row.** -/
theorem sample_only (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (a : ℕ) (k : KeptPlace)
    (hk : W.kept[a]? = some k) (Sl : Slots s K cs l W ids mem row a k) (sample : OnBytes.Row) :
    OnlyAt cs l ids
      (fun o part J => o = k.anew → part = Part.main →
        J % 2 ^ k.rowBits < k.rows ∧ J / 2 ^ k.rowBits < s.C.l)
      (sampleRow W k sample) := fun o part J hin hne =>
  keptForm_only D DK member a k hk Sl (formOn sample) o part J hin hne

/-- The indices of which claim_only speaks. -/
def InClaim (s : Sg) (W : SwitchFrame) (o : ℕ) (part : Part) (J : ℕ) : Prop :=
  (o = W.g → part = Part.main → J < 2 ^ W.tableBits) ∧
    ∀ k ∈ W.kept, o = k.anew → part = Part.main →
      J % 2 ^ k.rowBits < k.rows ∧ J / 2 ^ k.rowBits < s.C.l

/-- **The carried claim's row.** -/
theorem claim_only (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (old : SingleRows) (ks : List KeptPlace)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ClaimOK s K cs l W ids mem row pl old ks) :
    OnlyAt cs l ids (InClaim s W) (carriedOf W old ks) := by
  intro o part J hin hne
  have hl : s.C.l = 2 ^ W.code.logEll := by rw [D.codeC]; exact F.pow
  have hz : W.zk.ell = s.Z.l := by rw [D.codeZ]; rfl
  have hne' : coefAt ((List.range old.masks).foldl
      (fun (r : OnBytes.Row) j =>
        switchAddRestE r W.g W.restPart
          (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j #[]).size)
          (old.d.getD j #[]))
      ((old.kept.toList.zip ks).foldl (fun (r : OnBytes.Row) p => W.addKept r p.2 p.1.c)
        (({} : OnBytes.Row).addForm W.g
          (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits)))) o part J ≠ 0 := hne
  rw [hm, show List.range 2 = [0, 1] from rfl, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    ← h0, ← h1,
    coefAt_restE_at _ _ _ _ _ _ (fun i k a b => F.mask1.incM i k a (lt_of_lt_of_le b Q.d1)),
    coefAt_restE_at _ _ _ _ _ _ (fun i k a b => F.mask0.incM i k a (lt_of_lt_of_le b Q.d0)),
    kept_fold_at, coefAt_addForm, coefAt_empty, zero_add] at hne'
  rcases add_ne hne' with u | u
  · rcases add_ne u with v | v
    · rcases add_ne v with w | w
      · obtain ⟨c, k1⟩ := ite_ne w
        clear w v u hne' hne
        obtain ⟨rfl, rfl⟩ := beq2 c
        by_contra no
        refine k1 (formAt_switchLift_off old.c _ _ _ _ Q.mainVars F.cutBits F.cutRow F.cutTab
            F.cutAl
          F.cutFirst J (hin.1 rfl rfl) fun j hj e => no ?_)
        rw [← e]
        exact named_g D _ (D.mainMsg ⟨j, by rw [hl]; exact hj⟩)
      · obtain ⟨p, hp, hf⟩ := list_sum_ne _ _ w
        obtain ⟨-, a, hk, Sl, -⟩ := Q.forms p hp
        exact keptForm_only D DK member a p.2 hk Sl p.1.c o part J
          (hin.2 p.2 (List.mem_of_getElem? hk)) hf
    · obtain ⟨c, k1⟩ := ite_ne v
      clear v u hne' hne
      obtain ⟨rfl, rfl⟩ := beq2 c
      obtain ⟨i, hi, e, -⟩ := stretchAt_ne k1
      rw [← e]
      exact named_g D _ (D.mask0Msg ⟨i, by rw [← hz]; exact lt_of_lt_of_le hi Q.d0⟩)
  · obtain ⟨c, k1⟩ := ite_ne u
    clear u hne' hne
    obtain ⟨rfl, rfl⟩ := beq2 c
    obtain ⟨i, hi, e, -⟩ := stretchAt_ne k1
    rw [← e]
    exact named_g D _ (D.mask1Msg ⟨i, by rw [← hz]; exact lt_of_lt_of_le hi Q.d1⟩)

end Join

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.keptForm_only
#print axioms VerifiableInference.Desc.First.K2Hands.sample_only
#print axioms VerifiableInference.Desc.First.K2Hands.claim_only
