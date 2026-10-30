-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Filling.lean: "(rec_gamma)" AND "LOC" AT THE LEDGER OF A PROOF FILE's SHARED
CHAIN, WITH THIS KIND's LETTERS FILLED: the clauses at blocks 3 and 4
(Johnson/Desc/K14/Law/LedgerRecLoc.lean: rec_clause, loc_clause) with the premises that are this
kind's law's PAID.

THE FILLING. The rows' classes on G_u, as slices of the group's list as it lies in the record: row
(rec_gamma) := the rows 0, …, answers - 1 · row (loc_x) := the rows answers, …, answers + n - 1
(RowsUL, Johnson/Desc/K14/Law/RowsCore.lean: said at a statement that has grown out of the
    record's). shape 3 | 4 | 5 := shapeM at 0 | answers | answers + n
open rows on G_u (Johnson/Desc/K14/Law/Shapes.lean, ShapesSend.lean: shapeK): tests with code.
nearU, recRow, omU: AS THE TABLE's FILES FILL THEM AT "LIN point": NearAt, RecAll and OmU at a
reader uR of the record: a letter here, with "where o_u is seated the reader is the record itself".
  sh_mem, start_sh, ins0 … outs2, open3, open4   the table, unfolded: which shared items are open in
                  front of blocks 3 and 4.
  promsAt_three, promsAt_four, promsAt_five   the promise's clauses there: the stored table's; the
                  shape; "no collision" at o_u.
  OmU, omU_ride   "Omega is, row by row of M, what u gives at the point's low part"; it rides.
  loc_piece_yes   a yes of the piece at "LOC" is a yes of loc at one round that draws n positions.
  rec_filled      **the clause at block 3.**
  loc_filled      **the clause at block 4.**
WHAT STAYS, AND WHOSE. hl: the wrap · hd, ho, he: the plan's · hid: the table's files' · the eight
equations of letters (rfl where the letters are so filled) · huR: the reader (the table's files') ·
hride: the stored table's promise and "no collision" at o_u ride past the block · hback, hdet: o_u's
pin (the pins' files') · hsmp: o_u's sample's rows ride (the sending kind's). What is not claimed.
NO MEMBER: no letters and statement are shown at which all premises hold together. A block
that refuses all meets the clause. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerRecLoc
import Johnson.Desc.K14.Law.ShapesSend

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest Strs)
open VerifiableInference.Desc.K1 (size_of_same)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Run.PQ (CK)

/-! ## The table, unfolded -/

/-- A shared item of a list. -/
theorem sh_mem (L : List ItemS) (i : ItemS) :
    (i.own = false ∧ i ∈ L) ↔ i ∈ L.filter fun j => !j.own := by
  rw [List.mem_filter]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨hm, by rw [h]; rfl⟩
  · rintro ⟨hm, h⟩
    refine ⟨?_, hm⟩
    cases ho : i.own
    · rfl
    · rw [ho] at h
      cases h

theorem start_sh (i : ItemS) : startSh i ↔ i ∈ [ItemS.pinT] := by
  unfold startSh
  rw [sh_mem]
  rfl

theorem ins0 (split : Bool) (i : ItemS) : insSh split 0 i ↔ i ∈ ([] : List ItemS) := by
  have hr : ((rowAtS split 0).ins ++ (rowAtS split 0).ctx).filter (fun j => !j.own) = [] := by
    cases split <;> rfl
  unfold insSh
  rw [sh_mem, hr]

theorem outs0 (split : Bool) (i : ItemS) : outsSh split 0 i ↔ i ∈ ([] : List ItemS) := by
  have hr : ((rowAtS split 0).outs ++ (rowAtS split 0).ctx).filter (fun j => !j.own) = [] := by
    cases split <;> rfl
  unfold outsSh
  rw [sh_mem, hr]

theorem ins1 (split : Bool) (i : ItemS) : insSh split 1 i ↔ i ∈ [ItemS.pinT] := by
  have hr : ((rowAtS split 1).ins ++ (rowAtS split 1).ctx).filter (fun j => !j.own) =
      [.pinT] := by
    cases split <;> rfl
  unfold insSh
  rw [sh_mem, hr]

theorem outs1 (split : Bool) (i : ItemS) :
    outsSh split 1 i ↔ i ∈ [ItemS.omU, .nearU, .recRow] := by
  have hr : ((rowAtS split 1).outs ++ (rowAtS split 1).ctx).filter (fun j => !j.own) =
      [.omU, .nearU, .recRow] := by
    cases split <;> rfl
  unfold outsSh
  rw [sh_mem, hr]

theorem ins2 (split : Bool) (i : ItemS) : insSh split 2 i ↔ i ∈ ([] : List ItemS) := by
  have hr : ((rowAtS split 2).ins ++ (rowAtS split 2).ctx).filter (fun j => !j.own) = [] := by
    cases split <;> rfl
  unfold insSh
  rw [sh_mem, hr]

theorem outs2 (split : Bool) (i : ItemS) :
    outsSh split 2 i ↔ i ∈ [ItemS.pin .oU, .row (.sample .oU)] := by
  have hr : ((rowAtS split 2).outs ++ (rowAtS split 2).ctx).filter (fun j => !j.own) =
      [.pin .oU, .row (.sample .oU)] := by
    cases split <;> rfl
  unfold outsSh
  rw [sh_mem, hr]

/-- The shared items that are open in front of block 3, but for those that its row names. -/
theorem open3 (split : Bool) (i : ItemS) (h : openSh split 3 i) (hn : ¬ insSh split 3 i) :
    i = .omU ∨ i = .nearU ∨ i = .row (.sample .oU) := by
  have h' : (((((startSh i ∧ ¬ insSh split 0 i) ∨ outsSh split 0 i) ∧ ¬ insSh split 1 i) ∨
      outsSh split 1 i) ∧ ¬ insSh split 2 i) ∨ outsSh split 2 i := h
  rw [start_sh, ins0, outs0, ins1, outs1, ins2, outs2] at h'
  rw [ins3] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, and_true] at h'
  tauto

/-- The like in front of block 4. -/
theorem open4 (split : Bool) (i : ItemS) (h : openSh split 4 i) (hn : ¬ insSh split 4 i) :
    i = .omU ∨ i = .row (.sample .oU) ∨ i = .row .recG := by
  have h' : ((((((startSh i ∧ ¬ insSh split 0 i) ∨ outsSh split 0 i) ∧ ¬ insSh split 1 i) ∨
      outsSh split 1 i) ∧ ¬ insSh split 2 i) ∨ outsSh split 2 i) ∧ ¬ insSh split 3 i ∨
      outsSh split 3 i := h
  rw [start_sh, ins0, outs0, ins1, outs1, ins2, outs2, ins3, outs3] at h'
  rw [ins4] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, and_true] at h'
  tauto

theorem promsAt_three (split : Bool) :
    promsAt split 3 = [.tablePromise, .shape 3, .noColl .oU] := by
  cases split <;> rfl

theorem promsAt_four (split : Bool) :
    promsAt split 4 = [.tablePromise, .shape 4, .noColl .oU] := by
  cases split <;> rfl

theorem promsAt_five (split : Bool) :
    promsAt split 5 = [.tablePromise, .shape 5, .noColl .oU] := by
  cases split <;> rfl

/-! ## What rides -/

variable {P₁ Cl Wt : Type} {Fr : Frame}

/-- **"Omega is, row by row of M, what u gives at the point's low part"**, at a reader uR of the
record and a reader omW of the witness's Omega. -/
def OmU (P : Par) (uR : St → St) (rg : Wt → Words GE) (omW : Wt → Nat → GE) (s : St) (w : Wt) :
    Prop :=
  ∀ y < P.S.matrixRows, omW w y = ∑ t ∈ Finset.range (2 ^ P.S.kLo),
    eqK ((s.loc.psiSh.take P.S.kLo).map OnBytes.Model.Reading.gl.val) t *
      uOf (uR s).loc (rg w) (t + 2 ^ P.S.kLo * y)

/-- It rides back past a step that leaves the small record. -/
theorem omU_ride (P : Par) (uR : St → St) (rg : Wt → Words GE) (omW : Wt → Nat → GE) (s s' : St)
    (w : Wt) (l : s'.loc = s.loc) (hu : uR s = s) (hu' : uR s' = s')
    (h : OmU P uR rg omW s' w) : OmU P uR rg omW s w := by
  unfold OmU at h ⊢
  rw [hu', l] at h
  rw [hu]
  exact h

/-- **A yes of the piece at "LOC"** is a yes of loc at one round that draws n positions. -/
theorem loc_piece_yes (P : Par) (b : Block (P₁ × St) Cl) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wt → Wt)
    (er : Err (uLT (ckP .two) [d])) {ns n : ℕ}
    (hd : SendsDraws (toRD d) ns 0 n P.S.fold.index.code.logN)
    (hl : ∀ t rs gs t', b.decide t rs gs = .ok t' → loc P t.2 rs gs = some t'.2)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) [d])) (c : (P₁ × St) × Fr.E.Str)
    (hout : (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ =
      some c) :
    ∃ r4 cols, loc P a.1.2 [r4] [cols] = some c.1.2 ∧ r4.drawn.poss.length = n := by
  have hd' := piece_groups (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt) a τ c
    hout
  have k4 := hl _ _ _ _ hd'
  obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k4
  rw [hr, hg] at k4
  refine ⟨r4, cols, k4, ?_⟩
  obtain ⟨m, cc, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m cc)] = [r4] := hr
  obtain rfl := (List.cons.inj hr').1
  rw [poss_shown hd m cc, List.length_ofFn]

variable (N : NumbersS) (Mg : MeaningS St P₁ Wt)
  (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl Wt) (l : List (Piece (ckP .two) Fr (P₁ × St) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- **"(rec_gamma)" at the ledger, this kind's letters filled.** -/
theorem rec_filled (P : Par) (rg : Wt → Words GE) (uR : St → St) (omW : Wt → Nat → GE)
    (e' nU nO : ℕ) (x : Piece (ckP .two) Fr (P₁ × St) Cl Wt) (ε : Err (uLT (ckP .two) x.ds))
    (hl : ∀ t rs gs t', x.b.decide t rs gs = .ok t' → laysRec P t.2 rs = some t'.2)
    (hid : ∀ v w, e₀ 3 v w = w)
    (huR : ∀ s, seatedUB P s = true → uR s = s)
    (hnU : Mg.nearU = fun s y w => NearAt OnBytes.Model.Reading.gl P (uR s) (rg w) (colsOf y.cell)
      e')
    (hrR : Mg.recRow = fun s w => RecAll OnBytes.Model.Reading.gl P (uR s) (rg w))
    (hoU : Mg.omU = OmU P uR rg omW)
    (hrG : Mg.row .recG = fun s w => RowsUL OnBytes.Model.Reading.gl 0 P.S.fold.index.answers s
      (rg w))
    (hS3 : Pm.shape 3 = shapeM P nU nO 0)
    (hS4 : Pm.shape 4 = shapeM P nU nO P.S.fold.index.answers)
    (hride : ∀ c, c = PromS.tablePromise ∨ c = PromS.noColl .oU → ∀ a τ b,
      onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      c.holds N Pm ((actQ N p l 3).2 a).1 (strsOfAct Fr ((actQ N p l 3).2 a)) →
      c.holds N Pm ((actQ N p l 4).2 b).1 (strsOfAct Fr ((actQ N p l 4).2 b)))
    (hback : ∀ a τ b w, onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 b) w →
      muQ N Mg p l (.pin .oU) 3 ((actQ N p l 3).2 a) w)
    (hsmp : ∀ a τ b w, onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      muQ N Mg p l (.row (.sample .oU)) 4 ((actQ N p l 4).2 b) w →
      muQ N Mg p l (.row (.sample .oU)) 3 ((actQ N p l 3).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 3 x ε := by
  have hshM : ∀ a, onQ₂ N Pm Oc split p l 3 a → shapeM P nU nO 0 a.1.2 = true := by
    intro a ha
    have h1 : Pm.shape 3 a.1.2 = true := ha.1 (.shape 3) (by rw [promsAt_three]; simp)
    rw [hS3] at h1
    exact h1
  have hsh : ∀ a, onQ₂ N Pm Oc split p l 3 a → shapeU P nU 0 a.1.2 = true :=
    fun a ha => ((shapeM_iff P nU nO 0 a.1.2).1 (hshM a ha)).1
  have hseat : ∀ a, onQ₂ N Pm Oc split p l 3 a → seatedUB P a.1.2 = true :=
    fun a ha => ((shapeU_iff P nU 0 a.1.2).1 (hsh a ha)).2.1
  have hyes : ∀ a τ b, x.ior.red.out a τ = some b →
      b.2 = x.ior.imp a.2 τ ∧ ∃ rs, laysRec P a.1.2 rs = some b.1.2 := by
    intro a τ b hout
    obtain ⟨hy, gs, hd⟩ := piece_yes x a τ b hout
    exact ⟨hy, _, hl _ _ gs _ hd⟩
  refine rec_clause N Mg Pm Oc split p l e₀ P rg x ε hl hid ?_ 0 ?_
    (fun a ha => on4_of_seatedUB P a.1.2 (hseat a ha))
    (fun a ha => ((shapeU_iff P nU 0 a.1.2).1 (hsh a ha)).2.2.2) ?_ hback ?_
  · intro a w ha h
    rw [hrR]
    show RecAll OnBytes.Model.Reading.gl P (uR a.1.2) (rg w)
    rw [huR _ (hseat a ha)]
    exact h
  · intro s w h
    rw [hrG] at h
    exact h
  · intro a τ b ha hout c hc
    rw [promsAt_four] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hride _ (Or.inl rfl) a τ b ha hout (ha.1 _ (by rw [promsAt_three]; simp))
    · show Pm.shape 4 b.1.2 = true
      rw [hS4]
      obtain ⟨_, rs, k⟩ := hyes a τ b hout
      have h4 := shapeM_rec P nU nO 0 a.1.2 b.1.2 rs k (hshM a ha)
      rw [Nat.zero_add] at h4
      exact h4
    · exact hride _ (Or.inr rfl) a τ b ha hout (ha.1 _ (by rw [promsAt_three]; simp))
  · intro a τ b w i ha hout _ ho hi hm
    obtain ⟨hy, rs, k⟩ := hyes a τ b hout
    obtain ⟨o, lo⟩ := onward_laysRec P a.1.2 b.1.2 rs k
    have sA := hseat a ha
    have sB := seatedUB_onward P a.1.2 b.1.2 o lo sA
    rcases open3 split i ho hi with rfl | rfl | rfl
    · have hm' : Mg.omU b.1.2 w := hm
      show Mg.omU a.1.2 w
      rw [hoU] at hm' ⊢
      exact omU_ride P uR rg omW a.1.2 b.1.2 w lo (huR _ sA) (huR _ sB) hm'
    · have hm' : Mg.nearU b.1.2 (strsOfAct Fr ((actQ N p l 4).2 b)) w := hm
      show Mg.nearU a.1.2 (strsOfAct Fr ((actQ N p l 3).2 a)) w
      rw [hnU] at hm' ⊢
      have hb : NearAt OnBytes.Model.Reading.gl P (uR b.1.2) (rg w) (tabOf b.2) e' := by
        rw [tabOf_cells]
        exact hm'
      rw [huR _ sB, hy, tabOf_imp] at hb
      have ha' := NearAt.back OnBytes.Model.Reading.gl P a.1.2 b.1.2 _ _ _ lo hb
      rw [tabOf_cells] at ha'
      show NearAt OnBytes.Model.Reading.gl P (uR a.1.2) (rg w) _ e'
      rw [huR _ sA]
      exact ha'
    · exact hsmp a τ b w ha hout hm

/-- **"LOC" at the ledger, this kind's letters filled.** -/
theorem loc_filled (P : Par) (rg : Wt → Words GE) (uR : St → St) (omW : Wt → Nat → GE)
    (nU nO : ℕ) (b : Block (P₁ × St) Cl) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wt → Wt)
    (er : Err (uLT (ckP .two) [d])) {ns n : ℕ}
    (hd : SendsDraws (toRD d) ns 0 n P.S.fold.index.code.logN) (ho : d.opens = []) (e' e : ℕ)
    (he : (2 ^ P.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (hl : ∀ t rs gs t', b.decide t rs gs = .ok t' → loc P t.2 rs gs = some t'.2)
    (hid : ∀ v w, e₀ 4 v w = w)
    (huR : ∀ s, seatedUB P s = true → uR s = s)
    (hnU : Mg.nearU = fun s y w => NearAt OnBytes.Model.Reading.gl P (uR s) (rg w) (colsOf y.cell)
      e')
    (hoU : Mg.omU = OmU P uR rg omW)
    (hrG : Mg.row .recG = fun s w => RowsUL OnBytes.Model.Reading.gl 0 P.S.fold.index.answers s
      (rg w))
    (hrL : Mg.row .loc = fun s w => RowsUL OnBytes.Model.Reading.gl P.S.fold.index.answers n s
      (rg w))
    (hS4 : Pm.shape 4 = shapeM P nU nO P.S.fold.index.answers)
    (hS5 : Pm.shape 5 = shapeM P nU nO (P.S.fold.index.answers + n))
    (hride : ∀ c, c = PromS.tablePromise ∨ c = PromS.noColl .oU → ∀ a τ y,
      onQ₂ N Pm Oc split p l 4 a → (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl
        Wt).ior.red.out a τ = some y →
      c.holds N Pm ((actQ N p l 4).2 a).1 (strsOfAct Fr ((actQ N p l 4).2 a)) →
      c.holds N Pm ((actQ N p l 5).2 y).1 (strsOfAct Fr ((actQ N p l 5).2 y)))
    (hback : ∀ a τ c w, onQ₂ N Pm Oc split p l 4 a →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ = some c →
      muQ N Mg p l (.pin .oU) 5 ((actQ N p l 5).2 c) w →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w)
    (hdet : ∀ a w w', onQ₂ N Pm Oc split p l 4 a →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w' → AgreeOn nU (rg w) (rg w'))
    (hsmp : ∀ a τ c w, onQ₂ N Pm Oc split p l 4 a →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ = some c →
      muQ N Mg p l (.row (.sample .oU)) 5 ((actQ N p l 5).2 c) w →
      muQ N Mg p l (.row (.sample .oU)) 4 ((actQ N p l 4).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 4 (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St)
      Cl Wt)
      ((posMaps d P.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)) := by
  have hshM : ∀ a, onQ₂ N Pm Oc split p l 4 a →
      shapeM P nU nO P.S.fold.index.answers a.1.2 = true := by
    intro a ha
    have h1 : Pm.shape 4 a.1.2 = true := ha.1 (.shape 4) (by rw [promsAt_four]; simp)
    rw [hS4] at h1
    exact h1
  have hsh : ∀ a, onQ₂ N Pm Oc split p l 4 a →
      shapeU P nU P.S.fold.index.answers a.1.2 = true :=
    fun a ha => ((shapeM_iff P nU nO _ a.1.2).1 (hshM a ha)).1
  have hseat : ∀ a, onQ₂ N Pm Oc split p l 4 a → seatedUB P a.1.2 = true :=
    fun a ha => ((shapeU_iff P nU _ a.1.2).1 (hsh a ha)).2.1
  refine loc_clause N Mg Pm Oc split p l e₀ P rg b base d ex er hd ho e' e he hl hid ?_
    P.S.fold.index.answers ?_ (fun a ha => on4_of_seatedUB P a.1.2 (hseat a ha))
    (fun a ha => ((shapeU_iff P nU _ a.1.2).1 (hsh a ha)).2.2.2) ?_ hback ?_ ?_
  · intro a w ha h
    rw [hnU]
    show NearAt OnBytes.Model.Reading.gl P (uR a.1.2) (rg w) _ e'
    rw [huR _ (hseat a ha)]
    exact h
  · intro s w h
    rw [hrL] at h
    exact h
  · intro a τ y ha hout c hc
    rw [promsAt_five] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hride _ (Or.inl rfl) a τ y ha hout (ha.1 _ (by rw [promsAt_four]; simp))
    · show Pm.shape 5 y.1.2 = true
      rw [hS5]
      obtain ⟨r4, cols, k4, hlen⟩ := loc_piece_yes P b base d ex er hd hl a τ y hout
      have h5 := shapeM_loc P nU nO _ a.1.2 y.1.2 r4 cols k4 (hshM a ha)
      rw [hlen] at h5
      exact h5
    · exact hride _ (Or.inr rfl) a τ y ha hout (ha.1 _ (by rw [promsAt_four]; simp))
  · intro a w w' ha h h'
    rw [((shapeU_iff P nU _ a.1.2).1 (hsh a ha)).2.2.1]
    exact hdet a w w' ha h h'
  · intro a τ y w i ha hout _ ho' hi hm
    obtain ⟨r4, cols, k4, _⟩ := loc_piece_yes P b base d ex er hd hl a τ y hout
    obtain ⟨o, lo⟩ := onward_loc P a.1.2 y.1.2 r4 cols k4
    have sA := hseat a ha
    have sB := seatedUB_onward P a.1.2 y.1.2 o lo sA
    rcases open4 split i ho' hi with rfl | rfl | rfl
    · have hm' : Mg.omU y.1.2 w := hm
      show Mg.omU a.1.2 w
      rw [hoU] at hm' ⊢
      exact omU_ride P uR rg omW a.1.2 y.1.2 w lo (huR _ sA) (huR _ sB) hm'
    · exact hsmp a τ y w ha hout hm
    · have hm' : Mg.row .recG y.1.2 w := hm
      show Mg.row .recG a.1.2 w
      rw [hrG] at hm' ⊢
      exact rowsUL_back OnBytes.Model.Reading.gl 0 P.S.fold.index.answers a.1.2 y.1.2 (rg w) o
        (by rw [lo]) (by rw [((shapeU_iff P nU _ a.1.2).1 (hsh a ha)).2.2.2, Nat.zero_add]) hm'

end Desc.K14.Law
