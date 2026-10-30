-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Cores.lean
(kind K9's soundness lemma; for the table of joints): THEOREMS: THE THREE PIECES' CORE LAWS, EACH
BETWEEN ITS OWN TWO RELATIONS, WITHOUT THE RIDERS. The joining's relations (LinkJoin.relJ, and relJR
of Law/RowsNumber.lean) hold at all four boundaries "every open row of the group holds" and, behind
the first piece, the context: conjuncts that the three laws only carry. A table that ties each block
by itself hands a block, behind it, only what that block's own row opens: so here each law is stated
with just what it spends.
  tot1, tot2    the two sentences between the pieces: "the quiet moves return some state t from here
                and the ledger's one sum at t is 0 at the data that the tables hold"; "the ledger's
                one sum here is 0 at these data".
  LastRowAt     the row that stands last in the segment's group holds on the tables.
  equation_last a yes of the one equation's step: if the group's last row behind holds, the one sum
                in front is 0. (Law/Hout.lean's oneEquation_joint asks every row behind.)
  core1         the batching's piece: in front: at the bound data every coefficient of the batched
                polynomial is 0; behind: tot1 AND THE CONTEXT (spent for the pin: two witnesses in
                the context name one table). At the cap.
  core2         the piece behind it: in front tot1; behind tot2. No context.
  core3         the one equation's piece: in front tot2; behind LastRowAt. No context.
  cores_light   **ALL THREE WITH THE BOOK-KEEPING AND THE NUMBER OUT OF THE PROMISE**
                (Law/OnAFree.lean, Law/RowsNumber.lean): at on0 alone; Rw stands beside tot1 behind
                the first piece, beside tot1 and tot2 at the second, beside tot2 in front of the
                third, which proves it from its own yes.
JoinAsks is taken whole; hcq and hce are not spent by the cores; h12 and hon3 are (the conditions
are handed on), and htabq, htab (the tables are the same in front and behind).
Not claimed: any clause of JoinAsks at a segment of the protocol; the ties to a table's items.

-/
import Johnson.Desc.First.Batch.Law.OnAFree
import Johnson.Desc.First.Batch.Law.KeepsField

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where Lens door equation)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (JoinAsks)
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err Doomed)

section
variable {T K : Type} [CommRing K]

/-- The row that stands last in the segment's group holds on the tables. -/
def LastRowAt (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
    ∀ row, G.rows.back? = some row → rowSum ρ a.d.st N tab row = ρ.val row.target

/-- **A yes of the one equation's step: the last row behind gives the one sum in front.** -/
theorem equation_last {Cl : Type} (X : Lens T) (ρ : Reading K) (p : K9.Where) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (N : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (P : ∀ a q G, X.get? s = some a → equation a.L a.F = .ok (q, G) →
      RowPremises a.L.check a.d.st N q)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k))
    (hh : LastRowAt X ρ N s' tab) : oneK X ρ s s (dataAt X s tab) = 0 := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv X p ft s rs cols s' k h
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have hb : SameBits a.d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp (door_group _ _ _ _ _ _ hdoor)
  have hg1 : d1.st.groups = a.d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨a', ha', hL', hd'⟩ :=
    lens s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha'
  have eL : a'.L = a.L := hL'.trans hL
  have eD : a'.d.st = out.d.st := hd'
  have hGb : a'.d.st.groups[a'.L.check.group]? = some { G0 with rows := G0.rows.push row } := by
    rw [eD, eL, ho]
    show (Slice.withRow d1.st a.L.check.group row).groups[a.L.check.group]? = _
    simp only [Slice.withRow, Array.getElem?_modify, if_true, hg1, hG0, Option.map_some]
  have hrow := hh a' ha' _ hGb row (by simp)
  rw [eD, rowSum_bits ρ _ _ hb] at hrow
  have e := asRow_sum ρ a.L.check q a.d d1 row N tab (equation_k9 _ _ _ _ hq) (P a q G ha hq) hr
  rw [hrow, sub_self] at e
  simp only [oneK, dataAt, ha]
  rw [← equation_total ρ _ a.L a.F G q hq]
  exact e.symm

end

variable {α W Cl : Type} {F : Frame}

/-- Behind the first piece. -/
def tot1 (ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E))
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (a : S × F.E.Str) (w : W) : Prop :=
  ∃ t, MovesYes atS (ms₂.map (·.move)) a.1 t [] ∧
    oneK atS Reading.gl t t (dataAt atS a.1 (tabOf a w)) = 0

/-- Behind the second piece. -/
def tot2 (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (a : S × F.E.Str) (w : W) :
    Prop :=
  oneK atS Reading.gl a.1 a.1 (dataAt atS a.1 (tabOf a w)) = 0

section
variable {φ : S → α} {Ok : α × Option Pub9 → Prop} {Fu : S → Prop} {p pw : Where}
  {ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)} {d N : ℕ} {b₁ b₂ b₃ : Block S Cl}
  {pb pq pe : Piece (ckP .two) F S Cl W} {on0 on1 on2 on3 : S × F.E.Str → Prop}
  {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}

/-- **The batching's piece, at the cap.** -/
theorem core1
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    pb.GoodIn on0 on1
      (fun a w => ∃ y, boundAt atS tabOf ctx a w y ∧
        ∀ x ∈ termsOf (fixed9 φ a.1) y (ms₁ ++ ms₂) 0, x.2 = 0)
      (fun b w => tot1 ms₂ tabOf b w ∧ ctx b w) := by
  have HF := fitsM_atS (K := Cb.Gl.E) φ H.hφ Ok Fu p
  have hdoor₁ := (join_doors H).1
  have hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64 := by
    intro r hr
    rw [H.hds, List.mem_singleton] at hr
    rw [hr]
    exact Nat.zero_le 64
  have hheld : AllHeldEx (fun _ _ => d) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 pb.ds := by
    rw [H.hds]
    exact (allHeldEx_one (fun _ _ => d) _ 0 (k9Round p) 0 (dsOf_k9Round p)).2
      (num_k9 d (k9Round p).entry.work H.hd)
  have herr : Err.le (allErr (fun _ _ => d) 0 pb.ds) pb.err := by
    rw [H.hcap]
    exact herr_cap d pb.ds hlog hheld
  refine goodIn_conseq pb
    (goodInQ_real (semOf Reading.gl atS (O9 φ Ok Fu)) b₁
      (fun q y => termsOf q y (ms₁ ++ ms₂) 0) d H.hok
      (fun s' y => ∃ t, MovesYes atS (ms₂.map (·.move)) s' t [] ∧
        oneK atS Reading.gl t t y = 0)
      (fun s rs cols s' k hr _ hs => by
        obtain ⟨r, x, a, o, cls, rfl, hx, ha, ho, hy⟩ := H.hb₁ _ s rs cols s' k hs
        refine ⟨x, by simp [hx], fun y hQ => ?_⟩
        obtain ⟨t, ht, h0⟩ := hQ
        have hv := value_at Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF (ms₁ ++ ms₂) H.hms
          H.hend s t a o x (cls ++ []) hr ha ho (by
            rw [List.map_append]
            exact movesYes_append atS _ _ _ _ _ _ _ hy ht) y
        exact hv.symm.trans h0)
      pb H.hpb H.hextb on0 on1 (boundAt atS tabOf ctx) H.hready H.h01
      (fun a w w' y y' ha h1 h2 => by rw [h1.2, h2.2, H.hpin a w w' ha h1.1 h2.1])
      (fun a τ b' w y ha hout hB => ⟨H.hcb a τ b' w ha hout hB.1, by
        obtain ⟨h1, h2⟩ := hdoor₁ a τ b' hout
        rw [hB.2, H.htabb a τ b' w ha hout]
        exact dataAt_door atS a.1 b'.1 h2 h1 _⟩)
      hlog (fun r hr => by
        rw [H.hbk] at hr
        exact nomatch hr) reading_inj herr)
    (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)
    (fun b' w _ h => by
      obtain ⟨⟨t, h1, h2⟩, h3⟩ := h
      exact ⟨_, ⟨h3, rfl⟩, t, h1, h2⟩)

/-- **The piece behind it.** -/
theorem core2
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    pq.GoodIn on1 on2 (tot1 ms₂ tabOf) (tot2 tabOf) := by
  have hq₂ : ∀ m ∈ ms₂.map (·.move), ∃ h, m = .quiet h := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.quiet q hq
  refine moves_goodIn atS (ms₂.map (·.move)) b₂ H.hb₂ pq H.hpq H.hextq _ _ _ _
    H.h12 (fun a τ b' w cls ha hout hy h => ?_)
  rw [movesYes_quiet atS _ hq₂ _ _ _ hy] at hy
  have h1 : oneK atS Reading.gl b'.1 b'.1 (dataAt atS b'.1 (tabOf b' w)) = 0 := h
  rw [H.htabq a τ b' w ha hout,
    dataAt_door atS a.1 b'.1 ((join_doors H).2 a τ b' hout) (H.hs1 a ha) _] at h1
  exact ⟨b'.1, hy, h1⟩

/-- **The one equation's piece.** -/
theorem core3
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    pe.GoodIn on2 on3 (tot2 tabOf)
      (fun e w => LastRowAt atS Reading.gl N e.1 (tabOf e w)) := by
  have lens : ∀ s a, (atS.get? s).isSome = true →
      ∃ a', atS.get? (atS.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st := fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨H.hon3 a τ b ha hout, ?_⟩
  intro w hw
  rw [H.hexte]
  obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpe hout
  obtain ⟨k, hstep0⟩ := fold_one hfold
  have hstep := H.hb₃ _ _ _ _ _ hstep0
  rw [H.htab a τ b w ha hout] at hw
  obtain ⟨a0, out, ha0, hdoor, _⟩ := oneEquation_inv atS pw F.ft a.1 _ _ b.1 k hstep
  refine equation_last atS Reading.gl pw F.ft a.1 _ _ b.1 k N (tabOf a w) lens
    (fun a1 q G h1 hq => ?_) hstep hw
  have e : a1 = a0 := Option.some.inj (h1.symm.trans ha0)
  subst e
  exact door_facts _ _ _ _ _ out N (H.hN a ha a1 h1) (H.inside a ha a1 h1) hdoor q G hq

end

/-- **All three, with the book-keeping and the number out of the promise.** -/
theorem cores_light (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N : ℕ) (b₁ b₂ b₃ : Block S Cl)
    (pb pq pe : Piece (ckP .two) F S Cl W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a) :
    pb.GoodIn on0 on1
        (fun a w => ∃ y, boundAt atS tabOf ctx a w y ∧
          ∀ x ∈ termsOf (fixed9 φ a.1) y (ms₁ ++ ms₂) 0, x.2 = 0)
        (fun b w => (tot1 ms₂ tabOf b w ∧ Rw b) ∧ ctx b w) ∧
      pq.GoodIn on1 on2 (fun a w => tot1 ms₂ tabOf a w ∧ Rw a)
        (fun b w => tot2 tabOf b w ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => tot2 tabOf a w ∧ Rw a)
        (fun e w => LastRowAt atS Reading.gl N e.1 (tabOf e w)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine goodIn_of_yes pb on0 on1 (fun a => k9OnA a.1 = true) _ _ ?_ fun a τ b _ hout => ?_
    · intro a ha
      by_cases hc : C (fixed9 φ a.1)
      · exact goodIn_conseq pb (core1 H) (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)
          (fun _ _ _ h => ⟨h.1.1, h.2⟩) a ⟨ha, hc⟩
      · exact Doomed.of_forall _ _ fun τ b hout =>
          ⟨h01 a τ b ha.1 hout, fun w hw => absurd (hR1 a τ b ha.1 hout hw.1.2) hc⟩
    · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
      obtain ⟨k, hs⟩ := fold_one hfold
      exact yes_onA p _ b₁ H.hb₁ _ _ _ _ _ k hs
  · exact goodIn_and pq (core2 H) (Q := fun a _ => Rw a) (Q' := fun b _ => Rw b)
      (fun a τ b _ ha hout hq => hR2 a τ b ha hout hq)
  · exact goodIn_conseq pe (goodIn_and pe (core3 H) (Q := fun a _ => Rw a) (Q' := fun _ _ => True)
        (fun a τ b _ ha hout _ => hR3 a τ b ha hout))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨h, trivial⟩)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_last
#print axioms VerifiableInference.Desc.K9L.core1
#print axioms VerifiableInference.Desc.K9L.core2
#print axioms VerifiableInference.Desc.K9L.core3
#print axioms VerifiableInference.Desc.K9L.cores_light
