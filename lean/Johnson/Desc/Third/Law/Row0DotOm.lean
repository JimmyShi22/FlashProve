-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0DotOm.lean: WHO PAYS DotOmAt. Of the claims of K14's eight blocks on the
shared chain ONE stays open behind "SPLIT": DotOmAt ((Dot)'s equation at the point and at o_omega's
number that the shared chain's record notes; Johnson/Desc/K14/Law/Borders.lean: claimsB's last
line; Base rides beside it). IT IS PAID BY THE LAST CHAIN's FIRST BLOCK ("K14, second part"): the
semantic (Dot) that row 0 concludes in front of that block (DotSem,
Johnson/Desc/Third/Law/Row0Words.lean: row0_backW) IS DotOmAt at the shared chain's last record,
given two equations between the last chain's first record and what was handed to the chain. One
structure of Prop, three definitions, theorems.

OBJECT   DotSem's: (batchLinearConstraintsSecondPart p).decide, through row0_backW. BorderIs': startAtEnds
         (Johnson/Desc/Third/Border.lean) and Desc.K14.ended (Johnson/Desc/K14/Blocks.lean).
         DotOmAt: a definition on K14's own record St.
USER     the field dot of RowZeroLeft (Johnson/Desc/Third/Law/Row0AtTable.lean), at a table whose
         letter Mg.dot is filled by DotOmAt (dotI): dot_field pays it. Behind it: whoever spends
         DotUAt.of_omega on the shared chain.
LETTERS  S := p.S · g := the first chain's one pending row's weights, read by the reading gl, AS
         THE LAST CHAIN's BORDER HOLDS THEM · d := the shared chain's last record · m := rg d w:
         the words that the witness gives at the SHARED chain's numbers: rg IS A FAMILY IN d: a
         message's seat is read off d's book · V := wv q w, W's words.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  BorderIs g d s       the two equations: the border's shared point is d's psi_sh; its weights read
                       to g.
  start₃E_border_row · borderIs_of_start   it holds at the record that the start returns, given that
                       what is handed of the shared end bears d's psi_sh.
  ended_shared · gOfS · borderIs_at_seat   AT THE SEATED TEXTS: the last chain's start startAtEnds
                       at what K14's shared seat's "ended" hands on of d: BorderIs (gOfS e₁) d s₀:
                       NO PREMISE BUT THE TWO YESES.
  omOf S d rg          Omega's reader: o_omega's words at d's own number and d's codes' layout.
  dotOmAt_of_dotSem    **the payer.**   dotSem_of_dotOmAt: back: nothing is lost in the exchange.
  dotI                 the filling of the table's letter Mg.dot.   dot_field: RowZeroLeft's field.
What is not claimed. (1) THAT THE WORDS OF THE LAST CHAIN's STATEMENT AT OMEGA's NEW NUMBER ARE
omOf's (Reads.omega at omW u := omOf p.S d (rg d)): had at rg d := wordsShared at
d's statement and book: Johnson/Desc/Third/Law/Row0AtWords.lean. AT A READER rg THAT IS NOT HANDED d
no fence is known at which reads, fence and dot hold together, unless the fence and the promise at
border 0 say that Omega's seat in d's book is the plan's. (2) K14's law on the shared chain
(row3to8) has g, wv AND rg as fixed letters in front of all records, at pieces over St: the step
"for each handed part q, and at the chain's last record d, call the law at g q | wv q | rg d,
through the lift" is typed nowhere. (3) Its shape is P14.par.S, this file's P₁₄.S: an equation,
owed. (4) That the record in front of the block IS the start's: the promise's matter. No member. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Borders
import Johnson.Desc.Third.Border
import Johnson.Desc.Third.Law.Row0AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt omegaOf DotEq)
open _root_.Run.PQ (CK)

variable {W : Type}

/-- The last chain's first record against what was handed: the shared point, the row weights. -/
structure BorderIs (g : Nat → GE) (d : St) (s : S₃) : Prop where
  psi : ∀ b, s.loc.border = some b → b.shared.psi = d.loc.psiSh
  g : ∀ b, s.loc.border = some b → ∀ y,
    (b.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum = g y

/-- Omega's reader: o_omega's words at the shared record's own number and layout. -/
def omOf (S : LinShape) (d : St) (rg : W → Words GE) : W → Nat → GE :=
  fun w => omegaOf d.loc (linLayOmega d.st.codes S) (rg w)

/-- **The payer of DotOmAt.** -/
theorem dotOmAt_of_dotSem (p : P₁₄) (g : Nat → GE) (d : St) (s : S₃) (rg : W → Words GE)
    (wv : W → Nat → GE) (w : W) (T : BorderIs g d s)
    (h : DotSem OnBytes.Model.Reading.gl p (omOf p.S d rg) wv s w) :
    DotOmAt p.S g d (rg w) (wv w) := by
  obtain ⟨b, hb, hd⟩ := h
  have eg : (fun y => (b.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum) = g :=
    funext (T.g b hb)
  rw [eg, T.psi b hb] at hd
  exact hd

/-- Back, where the two ends are at hand. -/
theorem dotSem_of_dotOmAt (p : P₁₄) (g : Nat → GE) (d : St) (s : S₃) (rg : W → Words GE)
    (wv : W → Nat → GE) (w : W) (T : BorderIs g d s) (b : Border) (hb : s.loc.border = some b)
    (h : DotOmAt p.S g d (rg w) (wv w)) :
    DotSem OnBytes.Model.Reading.gl p (omOf p.S d rg) wv s w := by
  have eg : (fun y => (b.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum) = g :=
    funext (T.g b hb)
  refine ⟨b, hb, ?_⟩
  rw [eg, T.psi b hb]
  exact h

/-- **What the start lays as the border**: the one pending row's weights, and what it was handed of
the shared chain's end, as it was handed. -/
theorem start₃E_border_row (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    ∃ r, pile₁ = [r] ∧ s₀.loc.border = some ⟨r.g, o⟩ := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i t ht
        have e : t = s₀ := Except.ok.inj h
        subst e
        have e₁ : t.loc.border = some ⟨f.g, o⟩ := by
          unfold start₃ at ht
          split at ht
          · have e := Option.some.inj ht
            subst e
            rfl
          · cases ht
        have e₂ : ∃ r, pile₁ = [r] ∧ f.g = r.g := by
          unfold firstOutFrom at hf
          split at hf
          · rename_i r
            try dsimp only at hf
            repeat' (split at hf)
            all_goals first | (cases hf; exact ⟨r, rfl, rfl⟩) | (cases hf)
          · cases hf
        obtain ⟨r, hr, hg⟩ := e₂
        exact ⟨r, hr, by rw [e₁, hg]⟩

/-- **BorderIs at the record that the start returns**: where what is handed of the shared chain's
end bears d's shared point, and g is the one pending row's weights, read. -/
theorem borderIs_of_start (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (r : TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ [r] o = .ok s₀) (d : St)
    (hpsi : o.psi = d.loc.psiSh) :
    BorderIs (fun y => (r.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum) d s₀ := by
  obtain ⟨r', hr, hb⟩ := start₃E_border_row codes S st₁ book₁ roots₁ w₁ own₁ mask₁ [r] o s₀ h
  obtain rfl : r = r' := List.head_eq_of_cons_eq hr
  refine ⟨fun b hb' => ?_, fun b hb' y => ?_⟩
  · obtain rfl : (⟨r.g, o⟩ : Border) = b := Option.some.inj (hb.symm.trans hb')
    exact hpsi
  · obtain rfl : (⟨r.g, o⟩ : Border) = b := Option.some.inj (hb.symm.trans hb')
    rfl

/-- What the last chain's start is handed of K14's own last record, through the shared seat's
"ended" (Johnson/Desc/K14/Blocks.lean) and the last chain's reader of it
(Johnson/Desc/Third/Border.lean): the record's own statement, book, shared point and o_omega's
number. -/
theorem ended_shared (d : St) (e : Proof.SharedEnd) (h : _root_.Desc.K14.ended d = some e) :
    (sharedOfEnd e).psi = d.loc.psiSh ∧ (sharedOfEnd e).omega = d.loc.oOmega ∧
      (sharedOfEnd e).st = d.st ∧ (sharedOfEnd e).book = d.book := by
  unfold _root_.Desc.K14.ended at h
  dsimp only at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- The row weights of the first chain's last record's first pending row, read. -/
def gOfS (s : First.S) : Nat → GE := fun y =>
  (((s.rows.head?.map (·.g)).getD []).map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum

/-- **BorderIs AT THE SEATED TEXTS**: at the record that the last chain's start (startAtEnds)
returns of the first chain's last record and of what K14's shared seat hands on of its last record
d. -/
theorem borderIs_at_seat {XiPub : Type} (p : P₁₄) (q : XiPub) (e₁ : First.S) (d : St)
    (e : Proof.SharedEnd) (s₀ : S₃) (he : _root_.Desc.K14.ended d = some e)
    (h : startAtEnds p q e₁ e = .ok s₀) : BorderIs (gOfS e₁) d s₀ := by
  unfold startAtEnds start₃F at h
  cases hf : firstOfS e₁ with
  | none => rw [hf] at h; cases h
  | some f =>
    rw [hf] at h
    have h' : start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (sharedOfEnd e) =
        .ok s₀ := h
    have hp : f.pending = e₁.rows := by
      unfold firstOfS at hf
      cases hx : e₁.firstEnd? with
      | none => rw [hx] at hf; cases hf
      | some x => rw [hx] at hf; cases hf; rfl
    obtain ⟨r, hr, _⟩ := start₃E_border_row _ _ _ _ _ _ _ _ _ _ _ h'
    rw [hr] at h'
    have hg : gOfS e₁ =
        fun y => (r.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum := by
      unfold gOfS
      rw [← hp, hr]
      rfl
    rw [hg]
    exact borderIs_of_start _ _ _ _ _ _ _ _ r _ s₀ h' d (ended_shared d e he).1

variable {P S₁ Cl Wt : Type} {C : CK} {Fr : Frame}

/-- **The filling of the table's letter Mg.dot**: (Dot), at the shared record's psi_sh. -/
def dotI (S : LinShape) (g : P × S₁ → Nat → GE) (rg : St → Wt → Words GE)
    (wv : P × S₁ → Wt → Nat → GE) : P × S₁ → St → Strs → Wt → Prop :=
  fun q d _ w => DotOmAt S (g q) d (rg d w) (wv q w)

/-- **RowZeroLeft's field dot, at that filling**, from the two equations inside the promise. -/
theorem dot_field (N : NumbersS) (Mg : MeaningS St (P × S₁) Wt) (Pm : PromMeaning St)
    (PL : PromMeaningL St S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop) (p : P₁₄)
    (g : P × S₁ → Nat → GE) (rg : St → Wt → Words GE) (wv : P × S₁ → Wt → Nat → GE)
    (hMg : Mg.dot = dotI p.S g rg wv)
    (hB : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
      BorderIs (g (a.1.1.1, a.1.1.2.1)) a.1.1.2.2 a.1.2) :
    ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
      DotSem OnBytes.Model.Reading.gl p
        ((fun u : P × S₁ × St => omOf p.S u.2.2 (rg u.2.2)) a.1.1)
        ((fun u : P × S₁ × St => wv (u.1, u.2.1)) a.1.1) a.1.2 w →
      Mg.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w := by
  intro a w ha hd
  rw [hMg]
  exact dotOmAt_of_dotSem p _ _ _ (rg a.1.1.2.2) _ w (hB a ha) hd

end VerifiableInference.Desc.Third.Law
