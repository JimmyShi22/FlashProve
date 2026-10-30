-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsAtS.lean: The kind "lookup" (K3): ITS THREE RUNS OF CLAIMS ("objects",
"planes", "join") AT THE RECORD S, READ THROUGH THE LENS atS OF THE KIND "batching" (K9;
Johnson/Desc/First/Batch/AtS.lean) AND IN THAT KIND's OWN WORLD worldAt
(Johnson/Desc/First/Batch/Law/Measure.lean). Statements and proofs. They are what that kind's
premise on a run of plain claims asks of a run, but for its letters on the other kinds, which stand
in files that are not in this library.

Main names:
  pf_link, pf_tl, pf_st, pf_book, pf_roots, pf_owed, pf_used:
    what S.putFork leaves.
  atS_putFork: THE LENS BEHIND putFork: where atS reads a part a and G has a.F's next slot, behind
    s.putFork G it reads a part with the ledger G and a's every other field.
  AtS2 seat: the seat reads s.fork?, lays by putFork, and its claims are plain forms.
  value_plain: a plain form's claim is worth its form.
  OnlyUnder F G: G parts from F at most in what lies under the slots and in the marks on the debts:
    so the sums, chi, the counts and the arrays are F's.
  Left a a₁ G: what a run leaves of the part: the ledger G; the segment's record, the statement,
    the rows owed, the slots used, the equations' indices as they were.
  run_atS: ONE LEMMA FOR THE THREE: from a law "the run is worth ..." (K3RunIsWorthAt,
    Johnson/Top/H/K3RunsLaw.lean) to the run at the lens and in K9's world.
  objects_atS: a yes of "objects": the part behind is a's with a mark on a debt; as many claims as
    g has rows; all plain; AT EVERY LATER LEDGER H, every segment's record L and all data y their
    worths in worldAt are the flat rows' residues at y's mask row: NOTHING OF THE CALLER.
  planes_atS: a yes of "planes": the part behind is a's with the leaves' stretch filled and a mark;
    three claims; plain; their worths are the three claims' flat terms AT THE WORTHS OF THE CALLER's
    FORMS bit | pin in that same world.
  join_atS: a yes of "join": a mark; one claim; plain; its worth is the join's flat term at the
    worths of the caller's key forms.

Limits. That the caller's forms' worths are functions of what is fixed before the draw and the data
is the calling kind's. HeardIs at an earlier ledger, the shape's test and the ledger's sizes are
premises: the promise on the fixed part is to give them.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Law.Measure
import Johnson.Top.H.Keep.K3Late

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims
open OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)
open VerifiableInference.Desc.K9 (atS usedOf owedOf laidOf)
open VerifiableInference.Desc.K9L (claimValue worldAt Bound)

/-! ## What putFork leaves -/

theorem pf_link (s : S) (G : Fork) : (s.putFork G).link? = s.link? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.link?, ho]
  | _ => rfl

theorem pf_tl (s : S) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.tl?, ho]
  | _ => rfl

theorem pf_st (s : S) (G : Fork) : (s.putFork G).st = s.st := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, ho]
  | _ => rfl

theorem pf_book (s : S) (G : Fork) : (s.putFork G).book = s.book := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, ho]
  | _ => rfl

theorem pf_roots (s : S) (G : Fork) : (s.putFork G).roots = s.roots := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, ho]
  | _ => rfl

theorem pf_owed (s : S) (G : Fork) : owedOf (s.putFork G) = owedOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, owedOf, ho]
  | _ => rfl

/-- The slots used: at an attention link they are read off the ledger's next slot. -/
theorem pf_used (s : S) (F G : Fork) (hF : s.fork? = some F) (hn : G.next = F.next) :
    usedOf (s.putFork G) = usedOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | att x =>
    have e : x.F = F := Option.some.inj hF
    show some G.next = some x.F.next
    rw [hn, e]
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, usedOf, ho]
  | _ => rfl

/-- G parts from F at most in what lies under the slots and in the marks on the debts. -/
def OnlyUnder (F G : Fork) : Prop := ∃ G0 i, Same F G0 ∧ G = G0.paid i

theorem onlyUnder_paid (F : Fork) (i : ℕ) : OnlyUnder F (F.paid i) := ⟨F, i, rfl, rfl⟩

/-- What a run leaves of the part. -/
structure Left (a a₁ : Desc.K9.Part) (G : Fork) : Prop where
  F : a₁.F = G
  L : a₁.L = a.L
  d : a₁.d = a.d
  owed : a₁.owed = a.owed
  used : a₁.used = a.used
  laid : a₁.laid = a.laid

/-- The part that the lens makes of a record and what its four readers give. -/
def partOf (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) (used : Nat) : Desc.K9.Part :=
  { owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
    d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }

/-- **The lens behind putFork.** -/
theorem atS_putFork (s : S) (a : Desc.K9.Part) (G : Fork) (h : atS.get? s = some a)
    (hn : G.next = a.F.next) : ∃ a₁, atS.get? (s.putFork G) = some a₁ ∧ Left a a₁ G := by
  have h' : (s.link?.bind fun L => s.fork?.bind fun F => s.tl?.bind fun tl =>
      (usedOf s).bind fun used => some (partOf s L F tl used)) = some a := h
  obtain ⟨L, hL, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨F, hF, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨tl, htl, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨used, hu, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain rfl := Option.some.inj h'
  have hG : (s.putFork G).fork? = some G := fork_putFork s F G hF
  refine ⟨partOf s L G tl used, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  show ((s.putFork G).link?.bind fun L => (s.putFork G).fork?.bind fun F =>
      (s.putFork G).tl?.bind fun tl => (usedOf (s.putFork G)).bind fun used =>
        some (partOf (s.putFork G) L F tl used)) = _
  rw [pf_link, hL, hG, pf_tl, htl, pf_used s F G hF hn, hu]
  show some (partOf (s.putFork G) L G tl used) = some (partOf s L G tl used)
  unfold partOf
  rw [pf_owed, pf_st, pf_book, pf_roots]

/-! ## The seat -/

/-- The seat reads the record's own open ledger, lays by putFork, and its claims are plain forms. -/
structure AtS2 (seat : Seat S Desc.Claim) : Prop where
  fork : ∀ s, seat.fork s = s.fork?
  mark : ∀ s G, seat.mark s G = s.putFork G
  form : ∀ a, (seat.claim a).form = a
  runs : ∀ a, (seat.claim a).runs = #[]
  eqs : ∀ a, (seat.claim a).eqFirst = none

/-- What atS reads as the ledger is what the record's own reader gives. -/
theorem fork_of_atS {s : S} {a : Desc.K9.Part} (h : atS.get? s = some a) : s.fork? = some a.F := by
  have h' : (s.link?.bind fun L => s.fork?.bind fun F => s.tl?.bind fun tl =>
      (usedOf s).bind fun used => some (partOf s L F tl used)) = some a := h
  obtain ⟨L, _, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨F, hF, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨tl, _, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨used, _, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain rfl := Option.some.inj h'
  exact hF

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A plain form's claim is worth its form. -/
theorem value_plain {seat : Seat S Desc.Claim} (hA : AtS2 seat) (W : World K) (x : Aff) :
    claimValue ρ W (seat.claim x) = x.value ρ W := by
  unfold claimValue
  rw [hA.form, hA.runs]
  simp

/-- K9's world is the world of the lookup's laws, at the entries that read the mask row alone. -/
theorem worldAt_eq (L : LinkCtx) (H : Fork) (y : Bound K) :
    ∃ entry : ℕ → ℕ → ℕ → K,
      worldAt ρ L H y = H.worldOf ρ (fun j => muOf y.mask (.mask j)) entry := ⟨_, rfl⟩

section
variable (seat : Seat S Desc.Claim) (hA : AtS2 seat) (hs : SeatFits seat (·.form)) (lm : ℕ)
include hA hs

/-- From a law "the run is worth ..." to the run at the lens and in K9's world. -/
theorem run_atS (run : ℕ → S → Except String (List Desc.Claim × S))
    (want : S → (K : Type) → [CommRing K] → Heard → ℕ → Rounds K → (_root_.Fo.Pl → K) → (Aff → K) →
      List K)
    (hW : K3RunIsWorthAt seat.fork seat.heard (·.form) lm run want)
    (hcl : ∀ n s c s', run n s = .ok (c, s') → ∃ l : List Aff, c = l.map seat.claim)
    (hmk : ∀ n s c s' F, seat.fork s = some F → Sized F → run n s = .ok (c, s') →
      ∃ G, s' = seat.mark s G ∧ OnlyUnder F G)
    {e e₁ : S} {a : Desc.K9.Part} {c : List Desc.Claim} {front jLK : ℕ} {g : Heard} {F0 : Fork}
    {rs : Rounds K} (ha : atS.get? e = some a) (hg : seat.heard e = some g)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rs)) (hL : _root_.Fo.Later F0 a.F)
    (hok : FoNums.ok g.shape = true) (hS : Sized a.F) (hr : run front e = .ok (c, e₁)) :
    ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧ seat.heard e₁ = some g ∧
      OnlyUnder a.F G ∧ _root_.Fo.Later a.F G ∧ Sized G ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ (L : LinkCtx) (H : Fork) (y : Bound K), _root_.Fo.Later G H →
        c.map (claimValue ρ (worldAt ρ L H y)) =
          want e K g jLK rs (muOf y.mask) fun x => x.value ρ (worldAt ρ L H y) := by
  have hF : seat.fork e = some a.F := (hA.fork e).trans (fork_of_atS ha)
  obtain ⟨G, f1, g1, l1, s1, n1, hv⟩ := hW K ρ g jLK rs F0 a.F front e e₁ c hg hF hI hL hok hS hr
  obtain ⟨G', rfl, hU⟩ := hmk front e c e₁ a.F hF hS hr
  obtain rfl : G' = G := Option.some.inj ((hs.markFork e a.F G' hF).symm.trans f1)
  rw [hA.mark] at g1 ⊢
  obtain ⟨a₁, h1, h2⟩ := atS_putFork e a G' ha n1
  obtain ⟨l, rfl⟩ := hcl front e c _ hr
  refine ⟨a₁, G', h1, h2, rfl, g1, hU, l1, s1, fun cl hcl' => ?_, fun L H y hH => ?_⟩
  · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hcl'
    exact hA.eqs x
  · have := hv H hH (muOf y.mask) (VerifiableInference.Desc.K9L.entryAt ρ L.arrayOf
      (treesFrame H.trees) y)
    refine Eq.trans (List.map_congr_left fun cl hcl' => ?_) this
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hcl'
    rw [value_plain ρ hA]
    show _ = Aff.value ρ _ (seat.claim x).form
    rw [hA.form]
    rfl

/-- **"objects".** -/
theorem objects_atS {e e₁ : S} {a : Desc.K9.Part} {c : List Desc.Claim} {front jLK : ℕ} {g : Heard}
    {F0 : Fork} {rs : Rounds K} (ha : atS.get? e = some a) (hg : seat.heard e = some g)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rs)) (hL : _root_.Fo.Later F0 a.F)
    (hok : FoNums.ok g.shape = true) (hS : Sized a.F)
    (hr : objectsRun seat front e = .ok (c, e₁)) :
    ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧ seat.heard e₁ = some g ∧
      OnlyUnder a.F G ∧ _root_.Fo.Later a.F G ∧ Sized G ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ (L : LinkCtx) (H : Fork) (y : Bound K), _root_.Fo.Later G H →
        c.map (claimValue ρ (worldAt ρ L H y)) =
          (endsOf g.shape lm jLK rs).rows.map (rowRes (muOf y.mask)) :=
  run_atS ρ seat hA hs lm (objectsRun seat)
    (fun _ _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν))
    (objects_worth seat _ hs lm)
    (fun n s c s' h => by
      obtain ⟨F, g, e1, e2, _⟩ := objects_cut seat h
      rw [objects_answer seat n e1 e2] at h
      exact ⟨_, (congrArg Prod.fst (Except.ok.inj h)).symm⟩)
    (fun n s c s' F hF _ h => by
      obtain ⟨F1, g, e1, _, e⟩ := objects_cut seat h
      obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
      exact ⟨_, e, onlyUnder_paid F _⟩)
    ha hg hI hL hok hS hr

/-- **"planes"**: down to the worths of the caller's forms. -/
theorem planes_atS (readers : Readers S) {e e₁ : S} {a : Desc.K9.Part} {c : List Desc.Claim}
    {front jLK : ℕ} {g : Heard} {F0 : Fork} {rs : Rounds K} (ha : atS.get? e = some a)
    (hg : seat.heard e = some g) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rs))
    (hL : _root_.Fo.Later F0 a.F) (hok : FoNums.ok g.shape = true) (hS : Sized a.F)
    (hr : planesRun seat lm readers front e = .ok (c, e₁)) :
    ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧ seat.heard e₁ = some g ∧
      OnlyUnder a.F G ∧ _root_.Fo.Later a.F G ∧ Sized G ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ (L : LinkCtx) (H : Fork) (y : Bound K), _root_.Fo.Later G H →
        c.map (claimValue ρ (worldAt ρ L H y)) =
          [claimLeaves g.shape lm jLK rs (muOf y.mask) fun col =>
              (bitOf readers e 0 col).value ρ (worldAt ρ L H y),
            claimBits g.shape lm jLK rs (muOf y.mask) fun col =>
              (bitOf readers e 1 col).value ρ (worldAt ρ L H y),
            Pin.countK g.shape lm fun col => (pinOf readers e col).value ρ (worldAt ρ L H y)] :=
  run_atS ρ seat hA hs lm (planesRun seat lm readers) _ (planes_worth seat _ hs lm readers)
    (fun n s c s' h => by
      obtain ⟨F, g, e1, e2⟩ := planes_heard seat lm readers h
      obtain ⟨_, rows, _, _, _, _, e, _⟩ := planesRun_cut seat lm readers e1 e2 h
      exact ⟨_, e⟩)
    (fun n s c s' F hF hS h => by
      obtain ⟨F1, g, _, e2⟩ := planes_heard seat lm readers h
      obtain ⟨G, hG, e⟩ := planes_fills seat lm readers hF e2 h
      exact ⟨_, e, G, _, (hideRun_ok F G _ _ _ hS hG).1, rfl⟩)
    ha hg hI hL hok hS hr

/-- **"join"**: down to the worths of the caller's key forms. -/
theorem join_atS (keys : S → Option (Array Aff)) {e e₁ : S} {a : Desc.K9.Part} {c : List Desc.Claim}
    {front jLK : ℕ} {g : Heard} {F0 : Fork} {rs : Rounds K} (ha : atS.get? e = some a)
    (hg : seat.heard e = some g) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rs))
    (hL : _root_.Fo.Later F0 a.F) (hok : FoNums.ok g.shape = true) (hS : Sized a.F)
    (hr : joinRun seat keys front e = .ok (c, e₁)) :
    ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧ seat.heard e₁ = some g ∧
      OnlyUnder a.F G ∧ _root_.Fo.Later a.F G ∧ Sized G ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ (L : LinkCtx) (H : Fork) (y : Bound K), _root_.Fo.Later G H →
        c.map (claimValue ρ (worldAt ρ L H y)) =
          [claimJoin g.shape lm jLK rs (muOf y.mask) fun k =>
            ((keysOf keys e).getD k (Aff.ofConst zeroE)).value ρ (worldAt ρ L H y)] :=
  run_atS ρ seat hA hs lm (joinRun seat keys) _ (join_worth seat _ hs lm keys)
    (fun n s c s' h => by
      obtain ⟨F, g, e1, e2⟩ := join_heard seat keys h
      obtain ⟨KF, _, _, e, _⟩ := joinRun_cut seat keys e1 e2 h
      exact ⟨[joinForm g KF], e⟩)
    (fun n s c s' F hF _ h => by
      obtain ⟨F1, g, _, e2⟩ := join_heard seat keys h
      obtain ⟨_, _, _, _, e⟩ := joinRun_cut seat keys hF e2 h
      exact ⟨_, e, onlyUnder_paid F _⟩)
    ha hg hI hL hok hS hr

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_atS
#print axioms VerifiableInference.OnPublicFiles.planes_atS
#print axioms VerifiableInference.OnPublicFiles.join_atS
#print axioms VerifiableInference.OnPublicFiles.atS_putFork
#print axioms VerifiableInference.OnPublicFiles.value_plain
#print axioms VerifiableInference.OnPublicFiles.run_atS
