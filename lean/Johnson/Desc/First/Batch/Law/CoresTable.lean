-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/CoresTable.lean
(kind K9's soundness lemma; for the table of joints): THEOREM: THE THREE PIECES' CORE LAWS
(Law/Cores.lean: cores_light) IN THE TABLE's OWN LETTERS
(Johnson/Desc/Sound/FormsQ): each piece between just what its row of the table closes and opens:
  the batching          in front: formsQ of the listed runs       behind: totalBQ, Rw, the context
  the block behind it   in front: totalBQ, Rw                     behind: totalQ, Rw
  the one equation      in front: totalQ, Rw                      behind: rowEqQ
  rowEqQ        A PROPOSAL FOR THE MEANING OF THE TABLE's ITEM "the segment's one equation: the
                list's last row": the row that stands last in the segment's group holds on the
                accessor's tables (LastRowAt at tabAt).
  PlaceRowAt, lastRow_of_place   the same by the row's place in the list: where the list has i + 1
                rows, the row at place i is the last.
  LastSays, lastRow_of_says   the same in the library's own sentence "a row says its claim of the
                words" (Means/Says.lean), which the closing's files take for the table's letter
                "row": it gives LastRowAt for a last row that has no coefficient on a table that is
                not there nor beyond the statement's oracle messages (hfit;
                value_plain_le).
  equation_elder   FOR THE RIDERS: an elder row (by its place) that holds behind the one equation
                holds in front of it.
  lastRow_of_group   where every open row of the group holds, the last one does: so a law that ends
                in front in "every open row holds" (the closing's) closes that item.
  zero_of_termsRuns, forms_of_many, numbered_snd   from "every coefficient is 0" to formsQ of an
                item, over a list of runs: AN ITEM MAY STAND FOR SEVERAL RUNS OR FOR NONE; of a
                run's terms only the coefficients are asked to be its values (whatever the
                exponents): plain claims have it by numbered_snd.
  cores_table   the three laws. Law/JoinTable.lean's conversions, without the riders. GENERAL IN THE
                MOVES BEHIND THE DRAW (ms1, with hterms: the two rows' terms are the runs' terms in
                a row): so it can be called at a link of the driver's, whose batching has one move:
                the adding of what the link's own gatherer gathers.
"items" is a free list: for a tie to the table it is to be all the names of the segment's forms.
  cores_table_more   the same with a sentence Wq more in front of the first law: FOR the table's two
                items of the sort "worth" that the batching's row closes too: under hW (Wq follows
                from the front of K9's law, a yes of the batching's sub-protocol and the relation
                behind it). goodIn_mono_yes: the rule.
NOT REACHED: hW at these two items.
Rw: the public sentence of Law/RowsNumber.lean; it stands beside totalBQ and totalQ,
for the filling of the two letters.
HYPOTHESES: cores_light's, at tabOf := the accessor; JoinTable's four: hs2, hbook2, htin, hitems.
Not claimed: any of them at a segment of the protocol; that the table's letter is filled so.

-/
import Johnson.Desc.First.Batch.Law.Cores
import Johnson.Desc.First.Batch.Law.JoinTable
import Johnson.Desc.Means.RowSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where Lens door equation)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (JoinAsks)
open _root_.Run (ckP)

/-- Where every open row of the group holds, the last one does. -/
theorem lastRow_of_group {T K : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (tab : Nat → OnBytes.Part → Nat → K) (h : GroupHoldsAt X ρ N s tab) :
    LastRowAt X ρ N s tab := fun a ha G hG row hr =>
  h a ha G hG row (by
    rw [Array.back?_eq_getElem?] at hr
    exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hr))

/-- The row at place i of the segment's group's list holds on the tables. -/
def PlaceRowAt {T K : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (N i : Nat) (s : T)
    (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
    ∀ row, G.rows[i]? = some row → rowSum ρ a.d.st N tab row = ρ.val row.target

/-- Where the list has i + 1 rows, the row at place i is the last. -/
theorem lastRow_of_place {T K : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (N i : Nat)
    (s : T) (tab : Nat → OnBytes.Part → Nat → K) (h : PlaceRowAt X ρ N i s tab)
    (hn : ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
      G.rows.size = i + 1) : LastRowAt X ρ N s tab := fun a ha G hG row hr =>
  h a ha G hG row (by
    rw [Array.back?_eq_getElem?, hn a ha G hG] at hr
    exact hr)

/-- The last row of the segment's group's list says its claim of the words, in the library's own
sentence (Johnson/Desc/Means/Says.lean). -/
def LastSays {T K : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (s : T)
    (m : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
    ∀ row, G.rows.back? = some row → OnBytes.Means.Says ρ a.d.st row m

/-- **From the library's sentence to the law's**, by value_plain_le: for a last row that
has no coefficient on a table that is not there nor on an oracle message beyond the statement's. -/
theorem lastRow_of_says {T K : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (m : Nat → OnBytes.Part → Nat → K) (h : LastSays X ρ s m)
    (hfit : ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
      ∀ row, G.rows.back? = some row → a.d.st.oracles.size ≤ N ∧
        (∀ o part, a.d.st.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) ∧
        ∀ o, a.d.st.oracles.size ≤ o → ∀ part J, ρ.val (row.coefficient o part J) = 0) :
    LastRowAt X ρ N s m := fun a ha G hG row hr => by
  obtain ⟨hN, habs, hoff⟩ := hfit a ha G hG row hr
  have h1 : OnBytes.Means.value ρ a.d.st row m = ρ.val row.target := h a ha G hG row hr
  rw [OnBytes.Means.value_plain_le ρ a.d.st row m N hN habs hoff] at h1
  exact h1

/-- **An elder row that holds behind the one equation holds in front of it**: the block pushes one
row at the list's end and turns no number of row bits. -/
theorem equation_elder {T K Cl : Type} [CommRing K] (X : Lens T) (ρ : Reading K) (p : K9.Where)
    (ft : Nat) (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (N i : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k))
    (hh : PlaceRowAt X ρ N i s' tab) : PlaceRowAt X ρ N i s tab := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv X p ft s rs cols s' k h
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have hb : SameBits a.d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  have hg1 : d1.st.groups = a.d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨a', ha', hL', hd'⟩ :=
    lens s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha'
  have eL : a'.L = a.L := hL'.trans hL
  have eD : a'.d.st = out.d.st := hd'
  intro a2 ha2 G0 hG0 r hr2
  obtain rfl : a2 = a := Option.some.inj (ha2.symm.trans ha)
  have hGb : a'.d.st.groups[a'.L.check.group]? = some { G0 with rows := G0.rows.push row } := by
    rw [eD, eL, ho]
    show (Slice.withRow d1.st a2.L.check.group row).groups[a2.L.check.group]? = _
    simp only [Slice.withRow, Array.getElem?_modify, if_true, hg1, hG0, Option.map_some]
  have h1 := hh a' ha' _ hGb r (by
    have hi : i < G0.rows.size := (Array.getElem?_eq_some_iff.1 hr2).1
    show (G0.rows.push row)[i]? = some r
    rw [Array.getElem?_push_lt hi]
    exact (Array.getElem?_eq_some_iff.1 hr2).2 ▸ rfl)
  rw [eD, rowSum_bits ρ _ _ hb] at h1
  exact h1

/-- The segment's one equation's row holds on the accessor's tables. -/
def rowEqQ (own : List (ℕ × ℕ)) (N : ℕ) (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  LastRowAt atS Reading.gl N s (tabAt own rd s)

/-- From the runs' terms in a row to each run's. -/
theorem zero_of_termsRuns {T P K : Type} [Zero K] (p : P) (y : Bound K) :
    ∀ (rl : List (TermedRun T P K)) (n : ℕ), (∀ x ∈ termsRuns p y rl n, x.2 = 0) →
      ∀ r ∈ rl, ∃ m, ∀ x ∈ r.tm m p y, x.2 = 0
  | [], _, _, r, hr => nomatch hr
  | r0 :: l, n, h, r, hr => by
    have e : termsRuns p y (r0 :: l) n = r0.tm n p y ++ termsRuns p y l (n + r0.len p) := rfl
    rw [e] at h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨n, fun x hx => h x (List.mem_append_left _ hx)⟩
    · exact zero_of_termsRuns p y l _ (fun x hx => h x (List.mem_append_right _ hx)) r hr

variable {α W Cl : Type} {F : Frame}

/-- **The front of K9's law gives an item's forms.** AN ITEM MAY STAND FOR SEVERAL RUNS, OR FOR
NONE: rs: its runs, each with its list of values; of a run's terms only THE COEFFICIENTS are asked
to be these values, whatever the exponents (so a run with equations of its own window is no
exception); EACH OF THE READER's FORMS' VALUES IS AMONG THE RUNS' VALUES: no more is asked, and no
more is spent: a run may have terms that the item's reader does not list (the approximate range
proof's run has four numbered terms in front of its single equations; the reader of that item lists
the single equations alone). (Law/AtTable.lean's forms_of_front: one run of plain claims, over the
steps' moves.) -/
theorem forms_of_many (Rd : K9.Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (rd : ℕ × ℕ → MsgQ) (a : K9.Part) (R : K9.Read) (q : α × Option Pub9)
    (rl : List (TermedRun S (α × Option Pub9) GQ))
    (rs : List (TermedRun S (α × Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ)))
    (hrs : ∀ x ∈ rs, x.1 ∈ rl ∧ ∀ n y, (x.1.tm n q y).map (·.2) = x.2 q y)
    (ha : atS.get? s = some a) (hR : Rd.forms piece run s = some R)
    (hin : K9.formsIn Rd own piece run s = true)
    (hvals : ∀ f ∈ R.forms, f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) ∈
      rs.flatMap fun x => x.2 q (dataQ own a rd))
    (h0 : ∀ x ∈ termsRuns q (dataQ own a rd) rl 0, x.2 = 0) :
    formsQ Rd own piece run s rd := by
  have hz : ∀ f ∈ R.forms, f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) = 0 := by
    intro f hf
    obtain ⟨x, hx, hv⟩ := List.mem_flatMap.1 (hvals f hf)
    obtain ⟨hr, hco⟩ := hrs x hx
    obtain ⟨m, hm⟩ := zero_of_termsRuns q (dataQ own a rd) rl 0 h0 x.1 hr
    rw [← hco m] at hv
    obtain ⟨t, ht, e⟩ := List.mem_map.1 hv
    rw [← e]
    exact hm t ht
  have hseg := K9.segAt_of_atS s a ha
  unfold K9.formsIn at hin
  rw [hseg, hR] at hin
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  exact ⟨a, R, hseg, hR, h1, fun f hf => ⟨List.all_eq_true.1 h2 f hf,
    hz f hf⟩⟩

/-- The coefficients of numbered terms are the values. -/
theorem numbered_snd {K : Type} : ∀ (l : List K) (n : ℕ), (numbered n l).map (·.2) = l
  | [], _ => rfl
  | v :: l, n => by
    simp only [numbered, List.map_cons, numbered_snd l (n + 1)]

/-- A good piece stays good between a weaker relation in front and a stronger one behind; THE
CONVERSION IN FRONT MAY SPEND THE SUB-PROTOCOL's YES AND THE RELATION BEHIND, at the witness that
the extractor makes. (Law/AtTable.lean's goodIn_mono sees the statement in front alone.) -/
theorem goodIn_mono_yes {T Cl W : Type} {C : _root_.Run.PQ.CK} {F : Frame}
    (p : Piece C F T Cl W) (on on' : T × F.E.Str → Prop) (R R' R₂ R₂' : T × F.E.Str → W → Prop)
    (h : p.GoodIn on on' R R')
    (hf : ∀ a τ b w₀, on a → p.ior.red.out a τ = some b → on' b → R₂' b w₀ →
      R a (p.ext a τ w₀) → R₂ a (p.ext a τ w₀))
    (hb : ∀ b w, on' b → R₂' b w → R' b w) : p.GoodIn on on' R₂ R₂' := by
  intro a ha
  refine _root_.Iop.Doomed.mono _ _ (fun τ hτ b hout => ?_) (h a ha)
  obtain ⟨h1, h2⟩ := hτ b hout
  exact ⟨h1, fun w hw => hf a τ b w ha hout h1 hw (h2 w (hb b w h1 hw))⟩

/-- **The three core laws in the table's letters, WITH A SENTENCE MORE IN FRONT OF THE FIRST.** Wq:
whatever the batching's row closes beside the forms (at a segment of the protocol: the two items of
the sort "worth" of the lookup on the digits). hW: it follows from the front of K9's law (every
term's coefficient is 0), and may spend a yes of the batching's sub-protocol and the relation behind
it: so the runs' own yeses, and the full state behind the runs behind the batching, are in hand. -/
theorem cores_table_more (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) GQ))
    (rl : List (TermedRun S (α × Option Pub9) GQ))
    (hterms : ∀ q y, termsOf q y (ms₁ ++ ms₂) 0 = termsRuns q y rl 0) (d N : ℕ)
    (b₁ b₂ b₃ : Block S Cl) (pb pq pe : Piece (ckP .two) F S Cl W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop) (ctx : S × F.E.Str → W → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a)
    (hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true)
    (hbook₂ : ∀ m ∈ ms₂.map (·.move), MoveBook m)
    (htin : ∀ a t, on1 a → MovesYes atS (ms₂.map (·.move)) a.1 t [] →
      K9.totalIn own t = true)
    (hitems : ∀ a w, on0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read)
      (rs : List (TermedRun S (α × Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))),
      atS.get? a.1 = some b ∧
      (∀ x ∈ rs, x.1 ∈ rl ∧
        ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
      Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
      ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
        rs.flatMap fun x => x.2 (fixed9 φ a.1) (dataQ own b (rdW w)))
    (Wq : S × F.E.Str → W → Prop)
    (hW : ∀ a τ b' w₀, on0 a → pb.ior.red.out a τ = some b' → on1 b' →
      ((totalBQ (afterOf (ms₂.map (·.move))) own b'.1 (rdW w₀) ∧ Rw b') ∧ ctx b' w₀) →
      ∀ y, boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a (pb.ext a τ w₀) y →
        (∀ x ∈ termsRuns (fixed9 φ a.1) y rl 0, x.2 = 0) → Wq a (pb.ext a τ w₀)) :
    pb.GoodIn on0 on1 (fun a w => (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧ Wq a w)
        (fun b w => (totalBQ (afterOf (ms₂.map (·.move))) own b.1 (rdW w) ∧ Rw b) ∧ ctx b w) ∧
      pq.GoodIn on1 on2
        (fun a w => totalBQ (afterOf (ms₂.map (·.move))) own a.1 (rdW w) ∧ Rw a)
        (fun b w => totalQ own b.1 (rdW w) ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => totalQ own a.1 (rdW w) ∧ Rw a)
        (fun e w => rowEqQ own N e.1 (rdW w)) := by
  obtain ⟨g1, g2, g3⟩ := cores_light C Rw φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
    on0 on1 on2 on3 (fun a w => tabAt own (rdW w) a.1) ctx H h01 hR1 hR2 hR3
  have part1 := H.hs1
  have hkd₂ : ∀ m ∈ ms₂.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.hkd q (List.mem_append_right _ hq)
  have hq₂ : ∀ m ∈ ms₂.map (·.move), ∃ h, m = .quiet h := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.quiet q hq
  have hdata : ∀ (a : S × F.E.Str) (w : W) (t : S), on1 a →
      MovesYes atS (ms₂.map (·.move)) a.1 t [] →
      dataAt atS t (tabAt own (rdW w) t) = dataAt atS a.1 (tabAt own (rdW w) a.1) := by
    intro a w t ha hy
    obtain ⟨e1, e2⟩ := tabAt_quiet own (rdW w) _ hkd₂ hbook₂ a.1 t [] (part1 a ha) hy
    rw [e1]
    exact dataAt_door atS a.1 t e2 (part1 a ha) _
  have toB : ∀ (b : S × F.E.Str) (w : W), on1 b →
      totalBQ (afterOf (ms₂.map (·.move))) own b.1 (rdW w) →
      tot1 ms₂ (fun a w => tabAt own (rdW w) a.1) b w := by
    rintro b w hb ⟨t, ht, _, hq⟩
    have hy := (after_iff _ hq₂ b.1 t).2 ht
    refine ⟨t, hy, ?_⟩
    rw [← hdata b w t hb hy]
    exact ((total_iff own (rdW w) t).1 hq).2
  have ofB : ∀ (a : S × F.E.Str) (w : W), on1 a →
      tot1 ms₂ (fun a w => tabAt own (rdW w) a.1) a w →
      totalBQ (afterOf (ms₂.map (·.move))) own a.1 (rdW w) := by
    rintro a w ha ⟨t, hy, h0⟩
    refine ⟨t, (after_iff _ hq₂ a.1 t).1 hy, htin a t ha hy, ?_⟩
    rw [← hdata a w t ha hy] at h0
    obtain ⟨_, e2⟩ := tabAt_quiet own (rdW w) _ hkd₂ hbook₂ a.1 t [] (part1 a ha) hy
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (part1 a ha)
    obtain ⟨x', hx', _⟩ := e2 x hx
    exact (total_iff own (rdW w) t).2 ⟨by simp [hx'], h0⟩
  refine ⟨goodIn_mono_yes pb _ _ _ _ _ _ g1 (fun a τ b' w₀ ha hout hb' hR h => ?_)
      (fun b w hb h => ?_),
    goodIn_mono pq _ _ _ _ _ _ g2 (fun a w ha h => ?_) (fun b w _ h => ?_),
    goodIn_mono pe _ _ _ _ _ _ g3 (fun a w ha h => ?_) (fun b w _ h => h)⟩
  · obtain ⟨y, hbd, hz⟩ := h
    refine ⟨fun e he => ?_, hW a τ b' w₀ ha hout hb' hR y hbd (by rw [← hterms]; exact hz)⟩
    obtain ⟨b, R, rs, hb, hrs, hR', hin, hv⟩ := hitems a (pb.ext a τ w₀) ha e he
    have ey : y = dataQ own b (rdW (pb.ext a τ w₀)) :=
      hbd.2.trans (data_at own (rdW (pb.ext a τ w₀)) a.1 b hb)
    rw [ey, hterms] at hz
    exact forms_of_many Rd own e.1 e.2 a.1 (rdW (pb.ext a τ w₀)) b R (fixed9 φ a.1) rl rs hrs hb hR'
      hin hv hz
  · exact ⟨⟨toB b w hb h.1.1, h.1.2⟩, h.2⟩
  · exact ⟨ofB a w ha h.1, h.2⟩
  · exact ⟨((total_iff own (rdW w) b.1).1 h.1).2, h.2⟩
  · exact ⟨(total_iff own (rdW w) a.1).2 ⟨hs2 a ha, h.1⟩, h.2⟩

/-- **The three core laws in the table's letters.** ms1: the moves behind the draw, WHATEVER THEIR
MAKE; rl: the runs whose terms in a row are the two rows of moves' terms (hterms): at a link of the
driver's: one move, the adding of what the link's gatherer gathers. -/
theorem cores_table (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) GQ))
    (rl : List (TermedRun S (α × Option Pub9) GQ))
    (hterms : ∀ q y, termsOf q y (ms₁ ++ ms₂) 0 = termsRuns q y rl 0) (d N : ℕ)
    (b₁ b₂ b₃ : Block S Cl) (pb pq pe : Piece (ckP .two) F S Cl W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop) (ctx : S × F.E.Str → W → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a)
    (hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true)
    (hbook₂ : ∀ m ∈ ms₂.map (·.move), MoveBook m)
    (htin : ∀ a t, on1 a → MovesYes atS (ms₂.map (·.move)) a.1 t [] →
      K9.totalIn own t = true)
    (hitems : ∀ a w, on0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read)
      (rs : List (TermedRun S (α × Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))),
      atS.get? a.1 = some b ∧
      (∀ x ∈ rs, x.1 ∈ rl ∧
        ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
      Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
      ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
        rs.flatMap fun x => x.2 (fixed9 φ a.1) (dataQ own b (rdW w))) :
    pb.GoodIn on0 on1 (fun a w => ∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w))
        (fun b w => (totalBQ (afterOf (ms₂.map (·.move))) own b.1 (rdW w) ∧ Rw b) ∧ ctx b w) ∧
      pq.GoodIn on1 on2
        (fun a w => totalBQ (afterOf (ms₂.map (·.move))) own a.1 (rdW w) ∧ Rw a)
        (fun b w => totalQ own b.1 (rdW w) ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => totalQ own a.1 (rdW w) ∧ Rw a)
        (fun e w => rowEqQ own N e.1 (rdW w)) := by
  obtain ⟨g1, g2, g3⟩ := cores_table_more C Rw φ Ok Fu p pw ms₁ ms₂ rl hterms d N b₁ b₂ b₃ pb pq
    pe on0 on1 on2 on3 ctx Rd own rdW items H h01 hR1 hR2 hR3 hs2 hbook₂ htin hitems
    (fun _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
  exact ⟨goodIn_mono pb _ _ _ _ _ _ g1 (fun _ _ _ h => h.1) (fun _ _ _ h => h), g2, g3⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.lastRow_of_group
#print axioms VerifiableInference.Desc.K9L.lastRow_of_place
#print axioms VerifiableInference.Desc.K9L.lastRow_of_says
#print axioms VerifiableInference.Desc.K9L.equation_elder
#print axioms VerifiableInference.Desc.K9L.forms_of_many
#print axioms VerifiableInference.Desc.K9L.goodIn_mono_yes
#print axioms VerifiableInference.Desc.K9L.cores_table_more
#print axioms VerifiableInference.Desc.K9L.cores_table
