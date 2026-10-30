-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyBattFacts.lean: THE KEY FILE's ROW 1.16: THE BOOK-KEEPING's FACTS AROUND THE BATCHING's SEAT, at the first chain's state: in the form of KeyCaller.lean (a caller takes mask entries too): CallGround serves both.
  afterBatt        the state behind the seat's yes (KeyBattSays.seat_says), by name
  sentB_batt · groupB_batt · rides_batt   as sentB_call · groupB_call · rides_call
  tA_16_17 · mB_16_17 · sz_16_17 · t_16_17 · c_16_17   the two halves (ties₁; core₁) of the book-keeping's step 16 → 17; they are joined in KeyStep16.lean. EARNED HERE: the chain has come to its end · the claim is laid · EVERY MASK ENTRY OF THE CLAIM STANDS AT THE PART «mask» (the clause of sizesB from border 17 on: by claim_parts: memberClaim's own text). HANDED IN, BY NAME: hM (the claim's masks name message 0 alone) · hK (every vector of the claim's row weights is Tensor.ok) · hst (PUBLIC: fewer stages than the program's «no number»: so that the fresh claim's own group, noId, names no group)
Nothing on soundness.
-/
import Johnson.RunOne.KeyCaller
import Johnson.Desc.Key.KeyBattSays
import Johnson.Desc.Key.KeyClaimFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)

/-- The state behind the seat's yes. -/
def afterBatt (s : FirstState) (rows : List TensorRow) (msg : Array OracleNotice) (row : TensorRow) (d' : PlainState) : FirstState :=
  { s with pile := rows, atEnd := true, owed := none, msgW := msg, lin := some { claim := memberClaim row }, d := d' }

section
variable {Cells M Smp Rec : Type} (G : Reading (Xi × FirstState) Cells M Smp Rec) (one : OneTime)
variable (s : FirstState) (rows : List TensorRow) (msg : Array OracleNotice) (row : TensorRow) (d' : PlainState)

theorem sentB_batt (H : CallGround s d') (k : Nat) : sentB (plan₁ one) (readers₁ one) (afterBatt s rows msg row d') k = sentB (plan₁ one) (readers₁ one) s k := by
  unfold sentB
  cases ho : (plan₁ one).orc k with
  | none => rfl
  | some o =>
    show (match d'.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = (match s.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false)
    have e := H.oracle o
    cases h1 : d'.st.oracles[o]? with
    | none =>
      rw [h1] at e
      cases h2 : s.d.st.oracles[o]? with
      | none => rfl
      | some x => rw [h2] at e; cases e
    | some x' =>
      obtain ⟨x, hx, e1, e2⟩ := oracle_call s d' H o x' h1
      rw [hx]
      show (x'.sampled && x'.sampleRows.size != 0) = (x.sampled && x.sampleRows.size != 0)
      rw [e1, e2]

theorem groupB_batt (H : CallGround s d') (ir : Bool) (n : Nat) : groupB (readers₁ one) (afterBatt s rows msg row d') ir n = groupB (readers₁ one) s ir n := by
  unfold groupB
  show (match ((readers₁ one).grpB s).bind fun g => d'.st.groups[g]? with | some Gr => Gr.inRun == ir && Gr.rows.size == n | none => false) = _
  rw [H.groups]
  rfl

/-- **KeyQuiet.Rides around the batching's seat**, at every open set without «pile». -/
theorem rides_batt (hG : ReadsL G) (H : CallGround s d') (O : List KItem) (hO : KItem.pile ∉ O) (p : Xi) : Rides G (readers₁ one) O p s (afterBatt s rows msg row d') :=
  { marked := rfl, pins := hG p s (afterBatt s rows msg row d') H.oracle H.book H.codes
    stmt := fun _ => ⟨H.tables, fun o x' h => oracle_call s d' H o x' h⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun h => absurd h hO
    grp := fun _ => ⟨rfl, fun g G' h => ⟨G', (show s.d.st.groups[g]? = some G' from H.groups ▸ h), rfl⟩⟩ }

theorem tA_16_17 (H : CallGround s d') (h : tiesA one 16 s = true) : tiesA one 17 (afterBatt s rows msg row d') = true := by
  unfold tiesA at h ⊢
  simp only [afterBatt, H.codes]
  simpa using h

theorem mB_16_17 (H : CallGround s d') (h : moreB 16 s = true) : moreB 17 (afterBatt s rows msg row d') = true := by
  -- By hand, with no simp: the clause on the claim is answered by 17 < 18, so that no kernel has to
  -- compute on afterBatt's own claim, whose numbers are noId = 2 ^ 32 - 1.
  have orL : ∀ a x : Bool, a = true → (a || x) = true := by
    intro a x e
    subst e
    rfl
  have orR : ∀ a x : Bool, x = true → (a || x) = true := by
    intro a x e
    subst e
    cases a
    · rfl
    · rfl
  have h1 := Bool.and_eq_true_iff.1 (show (_ && _) = true from h)
  have h2 := Bool.and_eq_true_iff.1 h1.1
  have h3 := Bool.and_eq_true_iff.1 h2.1
  have h4 := Bool.and_eq_true_iff.1 h3.1
  unfold moreB
  rw [show (afterBatt s rows msg row d').d.book = s.d.book from H.book,
    show (afterBatt s rows msg row d').d.roots = s.d.roots from H.roots,
    show (afterBatt s rows msg row d').d.st.groups = s.d.st.groups from H.groups]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨h4.1, orR _ _ rfl⟩,
      orL _ _ (decide_eq_true (by decide : (17 : Nat) < 18))⟩, h2.2⟩, h1.2⟩

theorem osize (H : CallGround s d') : d'.st.oracles.size = s.d.st.oracles.size := H.tables.1

theorem sz_16_17 (H : CallGround s d') (hM : listOfT ((memberClaim row).masks.toList.map (·.oracle)) = [0]) (hK : (memberClaim row).g.all (·.ok) = true)
    (h : sizesB one 16 s = true) : sizesB one 17 (afterBatt s rows msg row d') = true := by
  unfold sizesB at h ⊢
  simp only [afterBatt, H.groups, H.book, osize s d' H]
  simp [counts₁, hM, hK, claim_parts row] at h ⊢
  exact h

theorem t_16_17 (H : CallGround s d') (hM : listOfT ((memberClaim row).masks.toList.map (·.oracle)) = [0]) (hK : (memberClaim row).g.all (·.ok) = true)
    (h : ties₁ one 16 s = true) : ties₁ one 17 (afterBatt s rows msg row d') = true := by
  unfold ties₁ at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨tA_16_17 one s rows msg row d' H h.1.1, mB_16_17 s rows msg row d' H h.1.2⟩, sz_16_17 one s rows msg row d' H hM hK h.2⟩

theorem c_16_17 (H : CallGround s d') (hsz : s.d.st.groups.size ≤ noId)
    (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 17 (afterBatt s rows msg row d') = true := by
  have he : ((readers₁ one).eval (afterBatt s rows msg row d')).isNone = true := by
    show ((d'.st.groups[noId]?).bind fun Gr => Gr.rows[0]?).isNone = true
    rw [H.groups, Array.getElem?_eq_none hsz]
    rfl
  have hp : ((readers₁ one).pile (afterBatt s rows msg row d')).isSome = true := rfl
  have hd : doneB (plan₁ one) (readers₁ one) 2 2 (afterBatt s rows msg row d') = doneB (plan₁ one) (readers₁ one) 2 2 s := rfl
  simp only [core₁] at h ⊢
  simp only [sentB_batt one s rows msg row d' H, groupB_batt one s rows msg row d' H, hd, he, hp]
  simp at h ⊢
  exact ⟨h.1, h.2.1.1, h.2.2⟩

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.rides_batt
#print axioms Johnson.RunOne.KeyRows1.t_16_17
#print axioms Johnson.RunOne.KeyRows1.c_16_17
