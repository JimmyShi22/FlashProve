-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieThreeFront.lean: THE TIE t3 OF A LINK's THIRD PIECE (t3_eq,
TieThreeEq.lean) WITH TWO OF ITS EIGHT PREMISES ON THE STATE BEHIND THE PIECE (grp:
the link's check names the plan's group · rows: that group's list ends with the equation's row)
MOVED IN FRONT OF THE PIECE, WHERE FACTS ALONG "REACHED" STAND. Theorems.

WHY. grp_reached (Johnson/LPFK9R/GrpReached.lean) says "the group that the link's context
names is the plan's group of the segment" at the border IN FRONT of the one equation. t3_eq asked it
BEHIND. The one equation's yes leaves the link's context (door_link) and lays one row on that
group's
list (eq_lays, EqLays.lean): so both ride over the step.

What is said.
  `front_gives`: behind a yes of the one equation's step: the link's check names the group that it
    named in front; where that group's list had i rows in front it has i + 1.
  `EqRest`: what is left of EqRowAsks behind the piece: SIX fields: order · codes · shapes ·
numbers ·
    places · member.
  `t3_eq_front`: **t3 AT THE ONE EQUATION's PIECE**, ending in the field's own type: EqRest behind;
    in front: hg · hr · K9.totalIn · InsideAt · hstep.

Limits. PREMISES, all asked only inside the condition `onTR`, SHOWN AT NO STATE HERE: behind:
EqRest · in front: hg (grp_reached says it at "reached", in scope, for numbers with
groupAt l = l) · hr ("the group's list has just the rows that the plan lays in front of the
equation's": NOBODY's) · hT · hin · hstep (step_of_out, TieFronts.lean). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TieThreeEq
import Johnson.Desc.First.Link.Law.EqLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers rowSays wordsAtFirst)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- **OVER A YES OF THE ONE EQUATION's STEP: the group's number stays; its list grows by one.** -/
theorem front_gives {Cl : Type} (p : Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (n : ℕ) (hs : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', n))
    (g i : ℕ) (hg : ∀ x, atS.get? s = some x → x.L.check.group = g)
    (hr : ∀ G, s.st.groups[g]? = some G → G.rows.size = i) :
    (∀ a', atS.get? s' = some a' → a'.L.check.group = g) ∧
      ∀ G, s'.st.groups[g]? = some G → G.rows.size = i + 1 := by
  obtain ⟨a, row, G0, ha, hG0, El⟩ :=
    eq_lays p (K9.oneEquation (Cl := Cl) atS p) (fun _ _ _ _ _ h => h) ft s rs cols s' n hs
  have eg := hg a ha
  constructor
  · intro a' ha'
    obtain ⟨a0, out, ha0, hdoor, e⟩ := oneEquation_inv atS p ft s rs cols s' n hs
    obtain rfl : a = a0 := Option.some.inj (ha.symm.trans ha0)
    obtain ⟨a₁, e0, _, e2, _⟩ :=
      atS_reads s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
    rw [← e] at e0
    obtain rfl : a₁ = a' := Option.some.inj (e0.symm.trans ha')
    rw [e2]
    show out.L.check.group = g
    rw [door_link _ _ _ _ _ _ hdoor]
    exact eg
  · intro G hG
    rw [eg] at hG0
    have hgr := El.groups
    rw [eg] at hgr
    rw [hgr] at hG
    simp only [Array.getElem?_modify, if_true, hG0, Option.map_some] at hG
    rw [← Option.some.inj hG]
    show (G0.rows.push row).size = i + 1
    rw [Array.size_push, hr G0 hG0]

section
variable (cs : OnBytes.Codes) (ms : List Mem)

/-- **WHAT IS LEFT OF EqRowAsks BEHIND THE PIECE.** -/
structure EqRest (M : List OracleShape) (g N : ℕ) (s : S) : Prop where
  order : OnBytes.Means.InOrder s.st ∧ s.st.oracles.size ≤ N
  codes : s.st.codes = cs
  shapes : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = M[o]?
  numbers : ∀ (z : ℕ) (T : Tree), s.book.trees[z]? = some T → T.number = z
  places : ∀ o, o < s.st.oracles.size → ∃ q : ℕ × ℕ, s.book.place[o]? = some q ∧
    q.1 < s.book.trees.size
  member : ∀ G row, s.st.groups[g]? = some G → G.rows.back? = some row → ∀ o part J,
    Reading.gl.val (row.coefficient o part J) ≠ 0 → ∀ q, s.book.place[o]? = some q →
    ∃ y, (ms.find? fun y => decide (seatOf y = q)) = some y ∧ M[o]? = some (y.1.l.get y.2).1

end

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **t3 AT THE ONE EQUATION's PIECE, THE GROUP's TWO FACTS ASKED IN FRONT.** -/
theorem t3_eq_front {C : CK} (M : List OracleShape) (N : ℕ)
    (houts : (rowQ links pl k).outs = [.row m .equation])
    (hn : 0 < (𝔇.N.rowsAt m .equation).2)
    (hA : ∀ b, onK (k + 1) b → EqRest 𝔇.cs 𝔇.ms M (𝔇.N.groupAt m) N b.1)
    (hg : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → x.L.check.group = 𝔇.N.groupAt m)
    (hr : ∀ a, onK k a → ∀ G, a.1.st.groups[𝔇.N.groupAt m]? = some G →
      G.rows.size = (𝔇.N.rowsAt m .equation).1)
    (hT : ∀ a, onK k a → K9.totalIn own a.1 = true)
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, onK k a → pe.ior.red.out a τ = some b → ∃ p ft rs cols n,
      (K9.oneEquation (Cl := Claim) atS p).step ft a.1 rs cols = .ok (b.1, n)) :
    ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relRow own N rdW b w := by
  intro a τ b w ha hout hb h
  obtain ⟨p, ft, rs, cols, n, hs⟩ := hstep a τ b ha hout
  obtain ⟨g1, g2⟩ := front_gives p ft a.1 rs cols b.1 n hs _ _ (hg a ha) (hr a ha)
  have R := hA b hb
  have h1 : rowSays 𝔇.N (wordsAtFirst 𝔇.arr) m .equation (z, b.1) (strsOf F b.2) w :=
    h (.row m .equation) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  exact rowEq_of_says 𝔇.cs 𝔇.arr 𝔇.ms own M _ _ _ N hn b.1 w
    { order := R.order, grp := g1, rows := g2, codes := R.codes, shapes := R.shapes,
      numbers := R.numbers, places := R.places, member := R.member }
    (seats_first own p ft a.1 rs cols b.1 n hs (hT a ha))
    (rowInside_step 𝔇.cs 𝔇.ms own p ft a.1 rs cols b.1 n N hs (hin a ha)) h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.front_gives
#print axioms VerifiableInference.Desc.LinkJoin.t3_eq_front
