-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeams23.lean, OVER Johnson/Desc/Msg.lean (Wit.pad · Reading.lay) AND KeyRows23At.lean (Agree has «lay alike»; the last border's witness gets a pad) (firstOutFrom_spec | start₃_full say besides whose the border's row weights are: the one pending row's) (THE LAST CHAIN's CLAIMS READ ITS OWN RECORD: the claims' half PAYS THE TIES by unfolding the start: the border is ⟨the pending row's g, what the start was handed of the shared chain's end⟩ · the statement is the first chain's last · W's number counts its messages; firstOutFrom_spec | start₃_full stand here) («Starts» gives ALL FOUR of what the start is handed of the shared chain's end: statement · book · the shared point · Omega's number) (THE SEAM IS STATED AT TWO FRAMES: the rule lays each chain at a frame of its own (the keys and the first own tree's number differ): the oracles on the two sides are handed as y₂ | y₃ with «strsOf Fr₃ y₃ = strsOf Fr₂ y₂», which is rfl where the two frames have one depth and one list of trees) (Agree has recOf: the two readings give one record at the seam · «Starts» has its member at the key file's description's own start₃: starts_fkD). AT THE PROMISES AND CLAIMS OF Johnson/RunOne/KeyRows23At.lean: what stands at the last boundary, and what the seam between the shared and the last chain asks. Statements, with proofs where said.
  open₃_last | open₂_first …   the open sets at the chains' ends, as equations in the kernel (by decide)
  ends₃        PROVED: at the file's last boundary the claim L₃ 4 holds of every statement: nothing is open but «unmarked», which these states always meet: so the rules' premise «ends» is free
  start₃_spec  PROVED: what the last chain's start's yes gives of its first record: its statement IS the first chain's last; the own group is what firstOutFrom names; the border lies; both ends' codes are the plan's
  Seam₂L       THE STATEMENT: where the start returns s₃: L₃ 0 at ((x, s₁, s₂), s₃) gives L₂ 12 at ((x, s₁), s₂): item by item the same sentence on the same witness, under «Agree» (the two readings G₂ | G₃ are one reading seen from two
               records), K₁.lin = S, and «Starts» (the description's start is the last chain's own start₃E at the first chain's last state's four things and at a SharedOut with the shared chain's last statement)
  seam₂L       ITS PROOF · beneath: valOf_plan₃ · rowHolds_plan₃ · srowAt_plan₃ · pin_agree
  starts_fkD   PROVED: «Starts» HOLDS OF THE KEY FILE's DESCRIPTION's OWN start₃ (descriptionFromSource, of Johnson/Desc/Key/Desc.lean), at the plan's shape and codes: so that premise is no letter
Limits. Nothing on the promises' halves of the seams (on₂ 12 → on₃ 0; on₁ last → on₂ 0). Nothing on soundness.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (FirstOut SharedOut firstOutFrom start₃ start₃E)

theorem open₃_last : open₃ 4 = [.unmarked] := by decide
theorem open₃_first : open₃ 0 = end₂ := by decide
theorem open₂_last : open₂ 12 = end₂ := by decide
theorem open₂_first : open₂ 0 = seam := by decide

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- **At the file's last boundary the claim holds of every statement.** -/
theorem ends₃ [Inhabited Cells] [Inhabited M] (x : (P₃ × St₃) × Fr₃.E.Str) : L₃ F Fr₃ G₃ at_ S K₁ R 4 x := by
  refine ⟨⟨default, (), fun _ => default, fun _ _ => default⟩, fun i hi => ?_⟩
  rw [open₃_last] at hi
  cases List.mem_singleton.1 hi
  exact trivial

end

/-- **What the start's yes gives.** -/
theorem start₃_spec (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : St₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    ∃ f, firstOutFrom S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ = some f ∧ s₀.st = f.st ∧ s₀.loc.own = f.own ∧ s₀.loc.border.isSome = true ∧
      f.st.codes = codes ∧ o.st.codes = codes := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i s hs
        cases h
        unfold start₃ at hs
        split at hs
        · rename_i hc
          cases hs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨f, hf, rfl, rfl, rfl, hc.1.1, hc.1.2⟩
        · cases hs

/-- OVER THE NINTH's TEXT (Johnson/Desc/Third/State.lean: firstOutFrom): W's number, the own group's and the mask's are HANDED IN BY NAME; the eighth's text reckoned them off the statement's sizes. -/
theorem firstOutFrom_spec (S : LinShape) (st : Statement) (book : TreeBook) (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pile = some f) :
    f.st = st ∧ f.book = book ∧ f.roots = roots ∧ f.w = w ∧ f.own = own ∧ f.mask = mask ∧ ∃ r, pile = [r] ∧ f.g = r.g := by
  unfold firstOutFrom at h
  split at h
  · rename_i r
    split at h
    · dsimp only at h
      split at h
      · cases h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, r, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

/-- **The tie that the first chain's last promise must hold, since the start takes the three numbers by name**: the record's claim names W as the last message but one, the own group as the last group, and the message behind W as the mask. -/
def LinTie (s : FirstState) : Prop :=
  ∃ l, s.lin = some l ∧ l.w + 2 = (firstOf s).1.oracles.size ∧ l.own + 1 = (firstOf s).1.groups.size ∧ l.mask = some (l.w + 1)

/-- **What the start's yes gives without any tie**: the statement and the book are the first chain's last; the three numbers are those handed in. -/
theorem start₃_plain (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : St₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.st = st₁ ∧ s₀.book = book₁ ∧ s₀.loc.w = w₁ ∧ s₀.loc.own = own₁ ∧ s₀.loc.mask = mask₁ ∧
      ∃ f, firstOutFrom S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ = some f ∧ s₀.loc.border = some ⟨f.g, o⟩ := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      obtain ⟨e1, e2, -, e4, e5, e6, -⟩ := firstOutFrom_spec S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ f hf
      split at h
      · cases h
      · rename_i s hs
        cases h
        unfold start₃ at hs
        split at hs
        · cases hs
          exact ⟨e1, e2, e4, e5, e6, f, hf, rfl⟩
        · cases hs

/-- The tables' reader of the first chain's end, where the record names its claim. -/
theorem firstAt_eq (S : LinShape) (s : FirstState) (l : LinFirst) (hl : s.lin = some l) :
    firstAt S s = firstOutFrom S (firstOf s).1 (firstOf s).2.1 (firstOf s).2.2.1 l.w l.own l.mask (firstOf s).2.2.2 := by
  unfold firstAt
  rw [hl]
  rfl

/-- **What the start's yes gives, field by field.** -/
theorem start₃_full (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : St₃)
    (hw : w₁ + 2 = st₁.oracles.size) (ho : own₁ + 1 = st₁.groups.size) (hk : mask₁ = some (w₁ + 1)) (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.st = st₁ ∧ s₀.book = book₁ ∧ s₀.roots = 0 ∧ s₀.loc.w = st₁.oracles.size - 2 ∧ s₀.loc.own = st₁.groups.size - 1 ∧ s₀.loc.mask = some (st₁.oracles.size - 1) ∧
      s₀.loc.border.isSome = true ∧ s₀.loc.omega = noId ∧ s₀.loc.firstTree = book₁.trees.size + 1 ∧ 2 ≤ st₁.oracles.size ∧ 1 ≤ st₁.groups.size ∧
      ∃ f, firstOutFrom S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ = some f ∧ s₀.loc.border = some ⟨f.g, o⟩ ∧ ∃ r, pile₁ = [r] ∧ f.g = r.g := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      obtain ⟨e1, e2, e3, e4, e5, e6, e10⟩ := firstOutFrom_spec S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ f hf
      split at h
      · cases h
      · rename_i s hs
        cases h
        unfold start₃ at hs
        split at hs
        · rename_i hc
          cases hs
          simp only [Bool.and_eq_true, decide_eq_true_eq, VerifiableInference.Desc.Third.rootsB, beq_iff_eq] at hc
          refine ⟨e1, e2, rfl, ?_, ?_, ?_, rfl, rfl, ?_, by omega, by omega, f, hf, rfl, e10⟩
          · show f.w = st₁.oracles.size - 2
            rw [e4]; omega
          · show f.own = st₁.groups.size - 1
            rw [e5]; omega
          · show f.mask = some (st₁.oracles.size - 1)
            rw [e6, hk]; congr 1; omega
          · show f.roots + 1 = book₁.trees.size + 1
            rw [hc.2, e2]
        · cases hs

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- The two readings are one reading, seen from the two records on the two sides of the seam. -/
structure Agree (start : Xi → FirstState → St₂ → Except String St₃) : Prop where
  arr : G₃.arr = G₂.arr
  lay : G₃.lay = G₂.lay
  enc : G₃.enc = G₂.enc
  rad : G₃.rad = G₂.rad
  meets : G₃.meets = G₂.meets
  /-- AT THE RECORDS ON THE TWO SIDES OF THE SEAM ALONE (where the start returns s₃), AND AT THE MESSAGES WHOSE PIN IS OPEN THERE ALONE -/
  smp : ∀ (x : Xi) (s₁ : FirstState) (s₂ : St₂) (s₃ : St₃), start x s₁ s₂ = .ok s₃ →
    ∀ k ∈ pinned end₂, G₃.smp ((x, s₁, s₂), s₃) (at_ k).1 (at_ k).2 = G₂.smp ((x, s₁), s₂) (at_ k).1 (at_ k).2
  /-- the stored table's record, off the two records at the seam, is one -/
  recOf : ∀ (x : Xi) (s₁ : FirstState) (s₂ : St₂) (s₃ : St₃), start x s₁ s₂ = .ok s₃ →
    G₃.recOf ((x, s₁, s₂), s₃) = G₂.recOf ((x, s₁), s₂)

/-- The description's start is the last chain's own, at the first chain's last state's four things and at a SharedOut that holds the shared chain's last statement. -/
def Starts (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃) : Prop :=
  ∀ x s₁ s₂ s₃, start x s₁ s₂ = .ok s₃ → ∃ (o : SharedOut) (l : LinFirst), s₁.lin = some l ∧ (o.st = s₂.st ∧ o.book = s₂.book ∧ o.psi = s₂.loc.psiSh ∧ o.omega = s₂.loc.oOmega) ∧
    start₃E codes S (firstOf s₁).1 (firstOf s₁).2.1 (firstOf s₁).2.2.1 l.w l.own l.mask (firstOf s₁).2.2.2 o = .ok s₃

/-- **The seam between the shared and the last chain, the claims' half.** start: the description's start₃. -/
def Seam₂L (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃) : Prop :=
  Agree G₂ G₃ at_ start → K₁.lin = S → S.masksAhead = true → Starts S codes start → ∀ x s₁ s₂ s₃ (y₂ : Fr₂.E.Str) (y₃ : Fr₃.E.Str), strsOf Fr₃ y₃ = strsOf Fr₂ y₂ → LinTie s₁ → start x s₁ s₂ = .ok s₃ →
    L₃ F Fr₃ G₃ at_ S K₁ R 0 (((x, s₁, s₂), s₃), y₃) → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 12 (((x, s₁), s₂), y₂)

variable {F Fr₂ Fr₃ G₂ G₃ at_ S K₁ R enc rad}

/-- Below n the last chain's plan reads the witness as the first chain's does. -/
theorem valOf_plan₃ (n o : Nat) (h : o < n) (w : Wit Cells Unit M) : valOf (plan₃ K₁ n) R w o = valOf K₁ R w o := by
  funext part i
  have hne : (o == n) = false := by simpa using Nat.ne_of_lt h
  simp only [valOf, plan₃, hne]
  rfl

/-- So a row of a statement of n messages means one thing under both. -/
theorem rowHolds_plan₃ (St : Statement) (w : Wit Cells Unit M) (r : OnBytes.Row) :
    RowHolds R.same St (valOf (plan₃ K₁ St.oracles.size) R w) r ↔ RowHolds R.same St (valOf K₁ R w) r := by
  unfold RowHolds
  rw [sumE_congr St.oracles.size _ _ fun o ho => by rw [valOf_plan₃ St.oracles.size o ho w]]

theorem srowAt_plan₃ (St : Statement) (k : Nat) (hk : k ≠ 4) (w : Wit Cells Unit M)
    (h : srowAt R (plan₃ K₁ St.oracles.size) St k w) : srowAt R K₁ St k w := by
  obtain ⟨o, x, ho, hx, hs, hz, hr⟩ := h
  have hk' : (k == 4) = false := by simpa using hk
  refine ⟨o, x, ?_, hx, hs, hz, fun r hr' => (rowHolds_plan₃ St w r).1 (hr r hr')⟩
  simpa only [plan₃, hk'] using ho

theorem pin_agree {start : Xi → FirstState → St₂ → Except String St₃} (A : Agree G₂ G₃ at_ start) (k : Nat) (hk : k ∈ pinned end₂)
    (x : Xi) (s₁ : FirstState) (s₂ : St₂) (s₃ : St₃) (hs : start x s₁ s₂ = .ok s₃) (y : Strs)
    (w : Wit Cells Unit M) (h : PIN F G₃ (at_ k).1 (at_ k).2 ((x, s₁, s₂), s₃) y w) : PIN F G₂ (at_ k).1 (at_ k).2 ((x, s₁), s₂) y w := by
  obtain ⟨o, z, ho, hz, hm⟩ := h
  refine ⟨o, z, ho, (A.smp x s₁ s₂ s₃ hs k hk) ▸ hz, ?_⟩
  unfold Member msgOf at hm ⊢
  rw [A.arr, A.lay, A.enc, A.rad, A.meets] at hm
  exact hm

theorem seam₂L (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃) :
    Seam₂L F Fr₂ Fr₃ G₂ G₃ at_ S K₁ R enc rad codes start := by
  intro A hlin hm hst x s₁ s₂ s₃ y₂ y₃ hy ht hs ⟨w, hw⟩
  obtain ⟨o, l, hl, ⟨ho, -, hop, -⟩, he⟩ := hst x s₁ s₂ s₃ hs
  obtain ⟨l', hl', t1, t2, t3⟩ := ht
  have el : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst el
  obtain ⟨f', hf', e_st', e_own', -, c₁', c₂⟩ := start₃_spec codes S _ _ _ _ _ _ _ o s₃ he
  obtain ⟨e_st₁, -, -, e_w, e_own₁, -, -, -, -, h2, -, f, hf, eb, -⟩ := start₃_full codes S _ _ _ _ _ _ _ o s₃ t1 t2 t3 he
  have ef : f' = f := Option.some.inj (hf'.symm.trans hf)
  subst ef
  have e_st := e_st'
  have c₁ := c₁'
  have e_own : s₃.loc.own = f'.own := e_own'
  have e_n : nOwn s₃ = (firstOf s₁).1.oracles.size := by
    unfold nOwn
    rw [e_w]
    omega
  refine ⟨w, fun i hi => ?_⟩
  rw [open₂_last] at hi
  have hw0 : relAt F G₃ at_ (meaning₃ S K₁ R) (open₃ 0) ((x, s₁, s₂), s₃) (strsOf Fr₃ y₃) w := hw
  rw [hy] at hw0
  have hw' : ∀ i ∈ end₂, i.holds F G₃ at_ (meaning₃ S K₁ R) ((x, s₁, s₂), s₃) (strsOf Fr₂ y₂) w := by
    intro i hi; exact hw0 i (by rw [open₃_first]; exact hi)
  have H := hw' i hi
  simp only [end₂, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact pin_agree A _ (by decide) x s₁ s₂ s₃ hs _ w H
  · -- srow 0
    have H' : srowAt R (plan₃ K₁ (nOwn s₃)) s₃.st 0 w := by simpa [KItem.holds, meaning₃, eb] using H
    have : srowAt R K₁ (firstOf s₁).1 0 w := by
      rw [e_n, e_st₁] at H'
      exact srowAt_plan₃ _ 0 (by decide) w H'
    simpa [KItem.holds, meaning₂, readers₂] using this
  · exact pin_agree A _ (by decide) x s₁ s₂ s₃ hs _ w H
  · -- srow 2
    have H' : srowAt R (plan₃ K₁ (nOwn s₃)) s₃.st 2 w := by simpa [KItem.holds, meaning₃, eb] using H
    have : srowAt R K₁ (firstOf s₁).1 2 w := by
      rw [e_n, e_st₁] at H'
      exact srowAt_plan₃ _ 2 (by decide) w H'
    simpa [KItem.holds, meaning₂, readers₂] using this
  · -- (Eval)
    have H' : rowsHold R.same s₃.st (valOf (plan₃ K₁ (nOwn s₃)) R w) s₃.loc.own 0 1 := by
      simpa [KItem.holds, meaning₃, claim₃, readers₃] using H
    obtain ⟨G, hG, hsz, -, hr⟩ := H'
    have hpos : 0 < G.rows.size := by omega
    have hmem : G.rows[0] ∈ (G.rows.toList.drop 0).take 1 := by
      cases hL : G.rows.toList with
      | nil => simp [← Array.length_toList, hL] at hpos
      | cons a l =>
        have : G.rows[0] = a := by simp [← Array.getElem_toList, hL]
        simp [this]
    have hrow := hr _ hmem
    rw [e_n, e_st₁] at hrow
    have hrow' := (rowHolds_plan₃ _ w _).1 hrow
    have hev : evalAt S s₁ = some G.rows[0] := by
      unfold evalAt
      rw [firstAt_eq S s₁ _ hl, hf]
      show (f'.st.groups[f'.own]?).bind (·.rows[0]?) = _
      rw [← e_st, ← e_own, hG]
      simp [hpos]
    have : ∃ r, evalAt S s₁ = some r ∧ RowHolds R.same (firstOf s₁).1 (valOf K₁ R w) r := ⟨_, hev, hrow'⟩
    simpa [KItem.holds, meaning₂, claim₂, readers₂] using this
  · exact pin_agree A _ (by decide) x s₁ s₂ s₃ hs _ w H
  · -- srow 4
    have H' : srowAt R (plan₂ S) o.st 4 w := by simpa [KItem.holds, meaning₃, eb] using H
    rw [ho] at H'
    simpa [KItem.holds, meaning₂] using H'
  · -- DotOm
    have hc : s₃.st.codes = s₂.st.codes := by rw [e_st, c₁, ← ho, c₂]
    have hd : DotOmAt R.same K₁.lin f'.g o.psi (omOf (plan₃ K₁ (nOwn s₃)) R s₃.st.codes w) (vOf' (plan₃ K₁ (nOwn s₃)) R s₃.st.codes w) := by
      simpa [KItem.holds, meaning₃, claim₃, readers₃, plan₃, eb] using H
    rw [hop] at hd
    have hg : (firstAt S s₁).map (·.g) = some f'.g := by
      rw [firstAt_eq S s₁ _ hl, hf]
      rfl
    have : ∃ g, (firstAt S s₁).map (·.g) = some g ∧
        DotOmAt R.same S g s₂.loc.psiSh (omOf (plan₂ S) R s₂.st.codes w) (vOf' (plan₂ S) R s₂.st.codes w) := by
      refine ⟨f'.g, hg, ?_⟩
      rw [hc, hlin] at hd
      have e1 : omOf (plan₃ K₁ (nOwn s₃)) R s₂.st.codes w = omOf (plan₂ S) R s₂.st.codes w := by
        funext y'; simp only [omOf, plan₃, plan₂, hlin]
      have e2 : vOf' (plan₃ K₁ (nOwn s₃)) R s₂.st.codes w = vOf' (plan₂ S) R s₂.st.codes w := by
        funext c'; simp only [vOf', plan₃, plan₂, hlin]
      rw [e1, e2] at hd
      exact hd
    simpa [KItem.holds, meaning₂, claim₂, readers₂, plan₂] using this

end

/-- **«Starts» has its member: the key file's description's own start** (descriptionFromSource, in Johnson/Desc/Key/Desc.lean). -/
theorem starts_fkD (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) :
    Starts X.chains.made.sized.key.once.shape X.chains.made.sized.key.codes fun x s₁ s₂ => (descriptionFromSource X N P).start₃ x s₁ s₂ := by
  intro x s₁ s₂ s₃ h
  have h' : (do
      let l ← named "the first chain's end names no W" s₁.lin
      let e₂ ← named "the shared chain's end: something is untested" (_root_.Desc.K14.ended s₂)
      start₃E X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape (firstOf s₁).1 (firstOf s₁).2.1
        (firstOf s₁).2.2.1 l.w l.own l.mask (firstOf s₁).2.2.2 (VerifiableInference.Desc.Third.sharedOfEnd e₂) : Except String St₃) = .ok s₃ := h
  cases hl : s₁.lin with
  | none => rw [hl] at h'; cases h'
  | some l =>
    rw [hl] at h'
    cases he : _root_.Desc.K14.ended s₂ with
    | none =>
      have h2 : (do
          let e₂ ← named "the shared chain's end: something is untested" (_root_.Desc.K14.ended s₂)
          start₃E X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape (firstOf s₁).1 (firstOf s₁).2.1
            (firstOf s₁).2.2.1 l.w l.own l.mask (firstOf s₁).2.2.2 (VerifiableInference.Desc.Third.sharedOfEnd e₂) : Except String St₃) = .ok s₃ := h'
      rw [he] at h2; cases h2
    | some e₂ =>
      have h2 : (do
          let e₂ ← named "the shared chain's end: something is untested" (_root_.Desc.K14.ended s₂)
          start₃E X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape (firstOf s₁).1 (firstOf s₁).2.1
            (firstOf s₁).2.2.1 l.w l.own l.mask (firstOf s₁).2.2.2 (VerifiableInference.Desc.Third.sharedOfEnd e₂) : Except String St₃) = .ok s₃ := h'
      rw [he] at h2
      refine ⟨VerifiableInference.Desc.Third.sharedOfEnd e₂, l, rfl, ?_, h2⟩
      unfold _root_.Desc.K14.ended at he
      split at he
      · cases he; exact ⟨rfl, rfl, rfl, rfl⟩
      · cases he

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.starts_fkD
#print axioms Johnson.RunOne.KeyRows23.ends₃
#print axioms Johnson.RunOne.KeyRows23.start₃_spec
#print axioms Johnson.RunOne.KeyRows23.start₃_full
#print axioms Johnson.RunOne.KeyRows23.start₃_plain
#print axioms Johnson.RunOne.KeyRows23.seam₂L
