-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeyRide23.lean. THE TABLE OF JOINTS OF THE KEY FILE,
ROWS 2.9, 2.10 AND 3.2 (the three later proximity tests): THE RIDERS OF EACH ROW's CLAIM's HALF:
every item that is open in front of the test and that it does not close holds in front, AT THE
WITNESS WITH THE ROW's MESSAGES LAID, if it holds behind. Statements with proofs. Each ride_… is
the premise "ride" of relAt_back_to (Johnson/RunOne/Law/KeyQuietSub.lean) at its row. In the make
of Johnson/RunOne/Law/KeyRide15.lean; the tools are Johnson/RunOne/Law/KeyRideTools.lean's.
OBJECT. KItem.holds at meaning₂ and meaning₃ (Johnson/RunOne/KeyRows23At.lean), at twelve, nine and
one item.
USER. The three rows' "back". Imported by K12Pays29.lean, K12PaysOfLaw210.lean and
K12Law32Core.lean in this folder.
LETTERS. The description F, the readings G₂ and G₃, the seats at_, the shape S, the first chain's
plan K₁, the reader R, enc and rad, the ring's reading ρ, the records a (in front) and b (behind),
the strings y and y', the witness w, THE LAID TABLES tbl (any).

THE ROWS:
  open29 … row32    the open sets, the riders and what the table's rows close, read and lay: by
                    evaluation in the kernel.
  sampled_of_msgIs  "message o is there and sampled", out of the book-keeping's own Bool.
  hmem_of_shape,    ride_29's hmem and hgO, out of shape₂'s clauses on the two groups' numbers and
                    on
  hgO_of_shape      G_omega's members (members_of_grpIs).
  words29, words210 the words at the riders' seats, out of StrsStay.
  Common            the facts that the nine riders of both rows of the shared chain read, one field
                    a fact.
  ride_common       these nine.
  ride_29           the twelve of row 2.9 (message 3 laid).
  ride_210          the nine of row 2.10 (message 5 laid).
  ride_32           the one of row 3.2: no premise.
  back_29 … back_32 THAT THEY FIT: each row's claim's half from its law (not paid here) and its
                    riders, by one call of relAt_back_to.
Limits. RULES: AS EMPTY AS THEIR PREMISES. No block is shown to have them.
(Where this and lean/THEOREM.md differ, the page holds.) No member of a row's
guard is shown. Nothing on soundness; nothing on hiding.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.RunOne.Law.KeyQuietSub
import Johnson.RunOne.Law.KeyRideTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.KeyRide23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.KeyRideTools

/-! ## 1 The table at the three rows -/

/-- What row 2.9, row 2.10 and row 3.2 close. -/
abbrev ins29 : List KItem :=
  [.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3]
abbrev ins210 : List KItem := [.claim 2 "FoldO", .srow 5, .pin 5]
abbrev ins32 : List KItem :=
  [.claim 1 "Eval", .claim 3 "Dot", .srow 0, .srow 2, .srow 4, .pin 0, .pin 2, .pin 4]

/-- The nine that ride across both tests of the shared chain. -/
abbrev nine : List KItem :=
  [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .pin 4, .srow 4, .claim 2 "DotOm"]

theorem row29 : (rows₂[9]?).map (fun r => (r.ins, r.ctx, r.lays)) =
    some (ins29, [KItem.pin 5, KItem.srow 5], [3]) := by
  decide

theorem row210 : (rows₂[10]?).map (fun r => (r.ins, r.ctx, r.lays)) =
    some (ins210, [KItem.pin 4, KItem.srow 4], [5]) := by
  decide

theorem row32 : (rows₃[2]?).map (fun r =>
  (r.ins, r.ctx, r.lays)) = some (ins32, [], [0, 2, 4]) := by
  decide

/-- **The twelve** of row 2.9. -/
theorem riders29 : (open₂ 9).filter (· ∉ ins29) =
    [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .pin 4, .srow 4, .pin 5, .srow 5,
      .claim 2 "DotOm", .claim 2 "FoldO"] := by
  decide

/-- **The nine** of row 2.10. -/
theorem riders210 : (open₂ 10).filter (· ∉ ins210) = nine := by
  decide

/-- **The one** of row 3.2. -/
theorem riders32 : (open₃ 2).filter (· ∉ ins32) = [.unmarked] := by
  decide

theorem pinned29 : pinned (open₂ 9) = [0, 2, 3, 4, 5] := by
  decide

theorem pinned210 : pinned (open₂ 10) = [0, 2, 4, 5] := by
  decide

/-- **"Message o is there and sampled"**, out of the book-keeping's own Bool on a message (shape₂'s
clause "Omega and the split are sampled", from border 6 on, asks it at messages 2 and 3). -/
theorem sampled_of_msgIs (st : Statement) (o n : Nat)
    (h : LKFU.Shape23.msgIs st o (some n) false = true) :
    ∃ x, st.oracles[o]? = some x ∧ x.sampled = true := by
  unfold LKFU.Shape23.msgIs at h
  cases hx : st.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨x, rfl, h.1.1⟩

/-- **A group's members**, out of the book-keeping's own Bool on a group. -/
theorem members_of_grpIs (st : Statement) (g : Nat) (ms : List Nat) (p q : Nat) (r : Bool)
    (h : LKFU.Shape23.grpIs st g ms p q r = true) (G₀ : OnBytes.Group)
    (hG : st.groups[g]? = some G₀) : G₀.members.toList = ms := by
  unfold LKFU.Shape23.grpIs at h
  rw [hG] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

/-- **ride_29's hmem**, out of two clauses of shape₂ at border 9: "the two groups' numbers" (G_omega
is
group 1) and "G_omega: members, open rows, begun" (its members are [2, 3]). -/
theorem hmem_of_shape (a : P₂ × St₂) (hg : a.2.loc.gOmega = 1) (p q : Nat) (r : Bool)
    (h : LKFU.Shape23.grpIs a.2.st 1 [2, 3] p q r = true) :
    ∀ G₀, a.2.st.groups[a.2.loc.gOmega]? = some G₀ → ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3 := by
  intro G₀ hG o ho
  rw [hg] at hG
  rw [members_of_grpIs a.2.st 1 [2, 3] p q r h G₀ hG] at ho
  simpa using ho

/-- **ride_29's hgO**, out of the clause "the two groups' numbers" at borders 9 and 10. -/
theorem hgO_of_shape (a b : P₂ × St₂) (ha : a.2.loc.gOmega = 1) (hb : b.2.loc.gOmega = 1) :
    b.2.loc.gOmega = a.2.loc.gOmega := hb.trans ha.symm

section
variable {XI : Type} (F : FileDescription XI) (at_ : Where)

/-- The words at the open pins' seats, out of what a block leaves of the strings. -/
theorem words29 (y y' : Strs) (Hy : StrsStay F at_ (open₂ 9) y y') :
    ∀ k ∈ [0, 2, 4, 5], wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2 :=
  fun k hk => Hy.word k (by
    rw [pinned29]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega)

theorem words210 (y y' : Strs) (Hy : StrsStay F at_ (open₂ 10) y y') :
    ∀ k ∈ [0, 2, 4], wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2 :=
  fun k hk => Hy.word k (by
    rw [pinned210]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega)

end

/-! ## 2 The shared chain's riders -/

section
variable {Cells M : Type} (S : LinShape) (K₁ : KPlan) (R : KRead Cells M)
  (enc : (Nat → E) → Nat → E) (rad : Nat)

theorem srow₂_low (k : Nat) (hk : k = 0 ∨ k = 2) (a : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (meaning₂ S K₁ R enc rad).srow k a y w = srowAt R K₁ ((readers₂ S).st₁ a.1) k w :=
  if_pos hk

theorem srow₂_own (k : Nat) (hk : ¬ (k = 0 ∨ k = 2)) (a : P₂ × St₂) (y : Strs)
    (w : Wit Cells Unit M) :
    (meaning₂ S K₁ R enc rad).srow k a y w = srowAt R (plan₂ S) a.2.st k w :=
  if_neg hk

/-- The three claims that ride, unfolded. Johnson/RunOne/KeyRow26.lean (eval₂_is) and
Johnson/RunOne/KeyRow28.lean (dotOm₂_is, foldO_is) hold the like,
as iffs at KItem.holds;
this file does not import them. -/
theorem eval₂_is (a : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (meaning₂ S K₁ R enc rad).claim 1 "Eval" a y w =
      ∃ r, (readers₂ S).eval a.1 = some r ∧
        RowHolds R.same ((readers₂ S).st₁ a.1) (valOf K₁ R w) r := by
  simp [meaning₂, claim₂]

theorem dotOm₂_is (a : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (meaning₂ S K₁ R enc rad).claim 2 "DotOm" a y w =
      ∃ g, (readers₂ S).g a = some g ∧ DotOmAt R.same (plan₂ S).lin g ((readers₂ S).psi a)
        (omOf (plan₂ S) R ((readers₂ S).st a.2).codes w)
        (vOf' (plan₂ S) R ((readers₂ S).st a.2).codes w) := by
  simp [meaning₂, claim₂]

theorem foldO₂_is (a : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (meaning₂ S K₁ R enc rad).claim 2 "FoldO" a y w =
      rowsHold R.same ((readers₂ S).st a.2) (valOf (plan₂ S) R w) ((readers₂ S).gO a.2) 0 1 := by
  simp [meaning₂, claim₂]

end

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
  (at_ : Where) (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E)
  (rad : Nat)

/-- **What the nine read**, one field a fact. a: the record in front of the test; b: behind. ks: the
riders' messages. -/
structure Common (ks : List Nat) (a b : P₂ × St₂) (y y' : Strs) : Prop where
  /-- srow 0, srow 2, (Eval), (DotOm): what was handed to the chain is not turned -/
  handed : b.1 = a.1
  /-- pin 0, pin 2, pin 4: the samples at their seats -/
  smp : ∀ k ∈ [0, 2, 4], G₂.smp b (at_ k).1 (at_ k).2 = G₂.smp a (at_ k).1 (at_ k).2
  /-- … and the words there -/
  word : ∀ k ∈ [0, 2, 4], wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2
  /-- srow 4; (DotOm) reads its first half, the codes -/
  stay : K1.SmpStay a.2.st b.2.st
  /-- srow 4: Omega (the own statement's message 2) is there and sampled in front -/
  omega : ∃ x, a.2.st.oracles[2]? = some x ∧ x.sampled = true
  /-- srow 4: its sample rows lie on its own tables -/
  omegaIn : SampleIn a.2.st 2
  /-- srow 0, srow 2: the like in the handed statement -/
  in₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → SampleIn ((readers₂ S).st₁ a.1) o
  /-- srow 0, srow 2: the first chain's plan sends these numbers to riders -/
  num₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ ks
  /-- (Eval): its row lies on the tables of a group whose members that plan sends to riders -/
  evalIn : ∀ r, (readers₂ S).eval a.1 = some r → ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1) Gr r ∧
    ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ ks
  /-- (DotOm): the shared point -/
  psi : b.2.loc.psiSh = a.2.loc.psiSh

variable {F G₂ at_ S K₁ R}

/-- **The nine ride.** -/
theorem ride_common {ls ks : List Nat} (tbl : Nat → M) (T : LayTies G₂ at_ R ls ks)
    (h0 : 0 ∈ ks) (h2 : 2 ∈ ks) (h4 : 4 ∈ ks) (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (a b : P₂ × St₂) (y y' : Strs) (w : Wit Cells Unit M) (C : Common F G₂ at_ S K₁ ks a b y y')
    (i : KItem) (hi : i ∈ nine) (hu : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w) :
    i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ ls tbl w) := by
  have low : ∀ k, k = 0 ∨ k = 2 → (meaning₂ S K₁ R enc rad).srow k b y' w →
      (meaning₂ S K₁ R enc rad).srow k a y (layAt at_ ls tbl w) := fun k hk h => by
    rw [srow₂_low S K₁ R enc rad k hk] at h ⊢
    rw [C.handed] at h
    have hk' : k ∈ [0, 2] := by rcases hk with rfl | rfl <;> simp
    exact ride_srowAt_same K₁ tbl w ρ T hsame _ k (C.in₁ k hk') (C.num₁ k hk') h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact ride_pinG F tbl T 0 h0 a b y y' w (C.smp 0 (by simp)) (C.word 0 (by simp)) hu
  · exact low 0 (Or.inl rfl) hu
  · exact ride_pinG F tbl T 2 h2 a b y y' w (C.smp 2 (by simp)) (C.word 2 (by simp)) hu
  · exact low 2 (Or.inr rfl) hu
  · have h : (meaning₂ S K₁ R enc rad).claim 1 "Eval" b y' w := hu
    show (meaning₂ S K₁ R enc rad).claim 1 "Eval" a y (layAt at_ ls tbl w)
    rw [eval₂_is] at h ⊢
    rw [C.handed] at h
    obtain ⟨r, hr, hb⟩ := h
    obtain ⟨Gr, hri, hn⟩ := C.evalIn r hr
    exact ⟨r, hr, ride_row K₁ tbl w ρ T hsame _ _ Gr r hri (fun _ _ _ => rfl) hn hb⟩
  · exact ride_pinG F tbl T 4 h4 a b y y' w (C.smp 4 (by simp)) (C.word 4 (by simp)) hu
  · have h : (meaning₂ S K₁ R enc rad).srow 4 b y' w := hu
    show (meaning₂ S K₁ R enc rad).srow 4 a y (layAt at_ ls tbl w)
    rw [srow₂_own S K₁ R enc rad 4 (by decide)] at h ⊢
    have ho : ∀ o, (plan₂ S).orc 4 = some o → o = 2 := fun o ho => by
      simpa [plan₂] using ho.symm
    exact ride_srowAt (plan₂ S) tbl w ρ T hsame a.2.st b.2.st 4 C.stay
      (fun o h' => by rw [ho o h']; exact C.omega) (fun o h' => by rw [ho o h']; exact C.omegaIn)
      (fun o h' j hj => by
        rw [ho o h'] at hj
        have e : j = 4 := by simpa [plan₂] using hj.symm
        rw [e]; exact h4) h
  · have h : (meaning₂ S K₁ R enc rad).claim 2 "DotOm" b y' w := hu
    show (meaning₂ S K₁ R enc rad).claim 2 "DotOm" a y (layAt at_ ls tbl w)
    rw [dotOm₂_is] at h ⊢
    obtain ⟨g, hg, hb⟩ := h
    have hg' : (readers₂ S).g a = some g := by
      have e : (readers₂ S).g a = (readers₂ S).g b := by
        show (firstAt S a.1.2).map (·.g) = (firstAt S b.1.2).map (·.g)
        rw [C.handed]
      rw [e]; exact hg
    refine ⟨g, hg', ?_⟩
    have e1 : (readers₂ S).psi b = (readers₂ S).psi a := C.psi
    have e2 : ((readers₂ S).st b.2).codes = ((readers₂ S).st a.2).codes := C.stay.1
    rw [e1, e2] at hb
    exact ride_dotOm (plan₂ S) tbl w T h4 h2 g _ _ hb

/-- **Row 2.10's riders.** tbl: ANY tables. -/
theorem ride_210 (tbl : Nat → M) (T : LayTies G₂ at_ R [5] [0, 2, 4])
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (a b : P₂ × St₂) (y y' : Strs)
    (w : Wit Cells Unit M) (C : Common F G₂ at_ S K₁ [0, 2, 4] a b y y') :
    ∀ i ∈ open₂ 10, i ∉ ins210 → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w →
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ [5] tbl w) := by
  intro i hi hn hu
  have hm : i ∈ (open₂ 10).filter (· ∉ ins210) := List.mem_filter.2 ⟨hi, decide_eq_true hn⟩
  rw [riders210] at hm
  exact ride_common ρ enc rad tbl T (by simp) (by simp) (by simp) hsame a b y y' w C i hm hu

/-- **Row 2.9's riders.** tbl: ANY tables. Beside the nine: pin 5, srow 5 and (FoldO). -/
theorem ride_29 (tbl : Nat → M) (T : LayTies G₂ at_ R [3] [0, 2, 4, 5])
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (a b : P₂ × St₂) (y y' : Strs)
    (w : Wit Cells Unit M) (C : Common F G₂ at_ S K₁ [0, 2, 4, 5] a b y y')
    (hsmp5 : G₂.smp b (at_ 5).1 (at_ 5).2 = G₂.smp a (at_ 5).1 (at_ 5).2)
    (hword5 : wordOf F y' (at_ 5).1 (at_ 5).2 = wordOf F y (at_ 5).1 (at_ 5).2)
    (hsplit : ∃ x, a.2.st.oracles[3]? = some x ∧ x.sampled = true)
    (hsplitIn : SampleIn a.2.st 3)
    (hgO : b.2.loc.gOmega = a.2.loc.gOmega)
    (hgrp : ∀ G', b.2.st.groups[a.2.loc.gOmega]? = some G' →
      ∃ G₀, a.2.st.groups[a.2.loc.gOmega]? = some G₀ ∧ G₀.rows = G'.rows)
    (hopen : OpenIn a.2.st a.2.loc.gOmega)
    (hmem : ∀ G₀, a.2.st.groups[a.2.loc.gOmega]? = some G₀ →
      ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3) :
    ∀ i ∈ open₂ 9, i ∉ ins29 → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w →
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ [3] tbl w) := by
  intro i hi hn hu
  have hm : i ∈ (open₂ 9).filter (· ∉ ins29) := List.mem_filter.2 ⟨hi, decide_eq_true hn⟩
  rw [riders29] at hm
  have com : i ∈ nine → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ [3] tbl w) :=
    fun h => ride_common ρ enc rad tbl T (by simp) (by simp) (by simp) hsame a b y y' w C i h hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact com (by simp)
  · exact ride_pinG F tbl T 5 (by simp) a b y y' w hsmp5 hword5 hu
  · have h : (meaning₂ S K₁ R enc rad).srow 5 b y' w := hu
    show (meaning₂ S K₁ R enc rad).srow 5 a y (layAt at_ [3] tbl w)
    rw [srow₂_own S K₁ R enc rad 5 (by decide)] at h ⊢
    have ho : ∀ o, (plan₂ S).orc 5 = some o → o = 3 := fun o ho => by
      simpa [plan₂] using ho.symm
    exact ride_srowAt (plan₂ S) tbl w ρ T hsame a.2.st b.2.st 5 C.stay
      (fun o h' => by rw [ho o h']; exact hsplit) (fun o h' => by rw [ho o h']; exact hsplitIn)
      (fun o h' j hj => by
        rw [ho o h'] at hj
        have e : j = 5 := by simpa [plan₂] using hj.symm
        rw [e]; simp) h
  · exact com (by simp)
  · have h : (meaning₂ S K₁ R enc rad).claim 2 "FoldO" b y' w := hu
    show (meaning₂ S K₁ R enc rad).claim 2 "FoldO" a y (layAt at_ [3] tbl w)
    rw [foldO₂_is] at h ⊢
    have e : (readers₂ S).gO b.2 = (readers₂ S).gO a.2 := hgO
    rw [e] at h
    refine ride_rowsHold (plan₂ S) tbl w ρ T hsame a.2.st b.2.st _ 0 1 C.stay hgrp hopen
      (fun G₀ hG₀ o ho => ?_) h
    rcases hmem G₀ hG₀ o ho with rfl | rfl
    · exact ⟨C.omega, fun k hk => by
        have e : k = 4 := by simpa [plan₂] using hk.symm
        rw [e]; simp⟩
    · exact ⟨hsplit, fun k hk => by
        have e : k = 5 := by simpa [plan₂] using hk.symm
        rw [e]; simp⟩

/-- **That ride_210 fits**: row 2.10's claim's half from its law (NOT PAID HERE) and its riders, by
one
call of relAt_back_to. r: the table's row there, said by its two lists (row210). -/
theorem back_210 (r : KRow) (hins : r.ins = ins210) (hctx : r.ctx = [KItem.pin 4, KItem.srow 4])
    (tbl : Nat → M) (T : LayTies G₂ at_ R [5] [0, 2, 4])
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (a b : P₂ × St₂) (y y' : Strs)
    (w : Wit Cells Unit M) (C : Common F G₂ at_ S K₁ [0, 2, 4] a b y y')
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w) →
      ∀ i ∈ r.ins, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ [5] tbl w))
    (h : relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (stepOpen (open₂ 10) r) b y' w) :
    relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 10) a y (layAt at_ [5] tbl w) :=
  KeyQuietSub.relAt_back_to F G₂ at_ (meaning₂ S K₁ R enc rad) r (open₂ 10) a b y y' w _
    (by
      rw [hctx, hins]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact ⟨by decide, by decide⟩)
    law (by rw [hins]; exact ride_210 ρ enc rad tbl T hsame a b y y' w C) h

/-- **That ride_29 fits**: the like at row 2.9 (row29). -/
theorem back_29 (r : KRow) (hins : r.ins = ins29) (hctx : r.ctx = [KItem.pin 5, KItem.srow 5])
    (tbl : Nat → M) (T : LayTies G₂ at_ R [3] [0, 2, 4, 5])
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (a b : P₂ × St₂) (y y' : Strs)
    (w : Wit Cells Unit M) (C : Common F G₂ at_ S K₁ [0, 2, 4, 5] a b y y')
    (hsmp5 : G₂.smp b (at_ 5).1 (at_ 5).2 = G₂.smp a (at_ 5).1 (at_ 5).2)
    (hword5 : wordOf F y' (at_ 5).1 (at_ 5).2 = wordOf F y (at_ 5).1 (at_ 5).2)
    (hsplit : ∃ x, a.2.st.oracles[3]? = some x ∧ x.sampled = true)
    (hsplitIn : SampleIn a.2.st 3)
    (hgO : b.2.loc.gOmega = a.2.loc.gOmega)
    (hgrp : ∀ G', b.2.st.groups[a.2.loc.gOmega]? = some G' →
      ∃ G₀, a.2.st.groups[a.2.loc.gOmega]? = some G₀ ∧ G₀.rows = G'.rows)
    (hopen : OpenIn a.2.st a.2.loc.gOmega)
    (hmem : ∀ G₀, a.2.st.groups[a.2.loc.gOmega]? = some G₀ →
      ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3)
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w) →
      ∀ i ∈ r.ins, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y (layAt at_ [3] tbl w))
    (h : relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (stepOpen (open₂ 9) r) b y' w) :
    relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 9) a y (layAt at_ [3] tbl w) :=
  KeyQuietSub.relAt_back_to F G₂ at_ (meaning₂ S K₁ R enc rad) r (open₂ 9) a b y y' w _
    (by
      rw [hctx, hins]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact ⟨by decide, by decide⟩)
    law
    (by
      rw [hins]
      exact ride_29 ρ enc rad tbl T hsame a b y y' w C hsmp5 hword5 hsplit hsplitIn hgO hgrp hopen
        hmem)
    h

end

/-! ## 3 The last chain's rider -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec)
  (at_ : Where) (S : LinShape) (K₁ : KPlan) (R : KRead Cells M)

/-- **Row 3.2's rider**: "unmarked" alone, which the last chain's meaning fills with True. -/
theorem ride_32 (tbl : Nat → M) (a b : P₃ × St₃) (y y' : Strs) (w : Wit Cells Unit M) :
    ∀ i ∈ open₃ 2, i ∉ ins32 → i.holds F G₃ at_ (meaning₃ S K₁ R) b y' w →
      i.holds F G₃ at_ (meaning₃ S K₁ R) a y (layAt at_ [0, 2, 4] tbl w) := by
  intro i hi hn _
  have hm : i ∈ (open₃ 2).filter (· ∉ ins32) := List.mem_filter.2 ⟨hi, decide_eq_true hn⟩
  rw [riders32] at hm
  have e : i = .unmarked := by simpa using hm
  subst e
  exact trivial

/-- **That ride_32 fits**: row 3.2's claim's half is its law (NOT PAID HERE) and nothing else. -/
theorem back_32 (r : KRow) (hins : r.ins = ins32) (hctx : r.ctx = []) (tbl : Nat → M)
    (a b : P₃ × St₃) (y y' : Strs) (w : Wit Cells Unit M)
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G₃ at_ (meaning₃ S K₁ R) b y' w) →
      ∀ i ∈ r.ins, i.holds F G₃ at_ (meaning₃ S K₁ R) a y (layAt at_ [0, 2, 4] tbl w))
    (h : relAt F G₃ at_ (meaning₃ S K₁ R) (stepOpen (open₃ 2) r) b y' w) :
    relAt F G₃ at_ (meaning₃ S K₁ R) (open₃ 2) a y (layAt at_ [0, 2, 4] tbl w) :=
  KeyQuietSub.relAt_back_to F G₃ at_ (meaning₃ S K₁ R) r (open₃ 2) a b y y' w _
    (by rw [hctx]; simp) law (by rw [hins]; exact ride_32 F G₃ at_ S K₁ R tbl a b y y' w) h

end

end Johnson.RunOne.Law.KeyRide23

#print axioms Johnson.RunOne.Law.KeyRide23.row29
#print axioms Johnson.RunOne.Law.KeyRide23.row210
#print axioms Johnson.RunOne.Law.KeyRide23.row32
#print axioms Johnson.RunOne.Law.KeyRide23.riders29
#print axioms Johnson.RunOne.Law.KeyRide23.riders210
#print axioms Johnson.RunOne.Law.KeyRide23.riders32
#print axioms Johnson.RunOne.Law.KeyRide23.ride_common
#print axioms Johnson.RunOne.Law.KeyRide23.ride_29
#print axioms Johnson.RunOne.Law.KeyRide23.ride_210
#print axioms Johnson.RunOne.Law.KeyRide23.ride_32
#print axioms Johnson.RunOne.Law.KeyRide23.back_29
#print axioms Johnson.RunOne.Law.KeyRide23.back_210
#print axioms Johnson.RunOne.Law.KeyRide23.back_32
#print axioms Johnson.RunOne.Law.KeyRide23.sampled_of_msgIs
#print axioms Johnson.RunOne.Law.KeyRide23.members_of_grpIs
#print axioms Johnson.RunOne.Law.KeyRide23.hmem_of_shape
#print axioms Johnson.RunOne.Law.KeyRide23.hgO_of_shape
#print axioms Johnson.RunOne.Law.KeyRide23.words29
#print axioms Johnson.RunOne.Law.KeyRide23.words210
#print axioms Johnson.RunOne.Law.KeyRide23.eval₂_is
#print axioms Johnson.RunOne.Law.KeyRide23.dotOm₂_is
#print axioms Johnson.RunOne.Law.KeyRide23.foldO₂_is
