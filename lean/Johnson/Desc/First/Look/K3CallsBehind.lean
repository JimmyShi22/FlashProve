-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsBehind.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS: THE
FIELD "behind" OF AttAtTable AND LayAtTable (the table's promise behind the block) BY ONE CALL OF
THE RULE FOR A QUIET ROW (onQ_step_quiet, Johnson/Desc/Sound/PromiseRidesQ.lean),
SIX PUBLIC ITEMS AND ONE SENTENCE PAID by what a yes of K3.block's decide makes and keeps
(Johnson/Desc/First/Look/K3CallsKeeps.lean, K3CallsLookOut.lean, K3LiveIs.lean, K3LeftItem.lean),
FOUR OF THE BOOK-KEEPING's Bools by kind-free rules. One structure, two theorems; and two that say
nothing new: att_behind_fits, lay_behind_fits: Lean lays calls_behind in the field's place in both
structures: so it IS that field's type. A tie: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table's promise onQ at border k + 1.
USER: K3CallsMeanOf.lean (it makes AttAtTable and LayAtTable: calls_behind is their field "behind");
  K3CallsAt.lean, K3CallsAtR.lean (calls_quiet).
LETTERS: general in the caller: attention, the layers and the head alike; pc: the table's piece of
  the lookup on the calls (2; at the head's segment 3); arrs: the plan's table of arrays at the
  link. The plan's number of slots is the parameters' own (P.ns).

PAID HERE, each through a tie of the filling (the structure's fields f...):
  lookOut m pc (k3OnOut) · ledger m (there and sized) · freeAbove m KEPT (free from the next slot
  on, and the ledger's number of slots is the plan's) · linkFresh m KEPT (nothing heard at the
  digits' seat; the open link's table of arrays) · left m (its Bool is true; its sentence pubP:
  k3LeftItem, Johnson/Desc/First/Look/K3LeftItem.lean: made by k3_calls_leftItem from what freeAbove
  and lookIn say of the ledger in front) · "frame.liveIs" KEPT.
PAID BY KIND-FREE RULES, from SameBut: rowsHeld, membersHeld (inside the rule for a quiet row: the
  statement's groups and the book's places are as they were) · shapeAt (shapeAt_rides through
  sameBut_shapeAt, Johnson/Desc/First/Look/K3ShapeBehind.lean) · bookAt (bookAt_step,
  Johnson/Desc/First/BookFit.lean).
TESTS ON THE TABLE AND THE NUMBERS, AS FIELDS: here, next (the places at k and k + 1) · quiet (paid
  by calls_quiet at every sort of segment) · stand (sameStand) · fit, tells (bookFit;
  block k tells no tree).
LEFT AS PREMISES (the structure's fields b...), each asked at a yes of the piece, under the promise
in front, no mark, with SameBut handed beside:
  bOrder: "in order" rides · bPub: every OTHER public item that is open or tied behind (look,
  callerIn, formsInT "objects", and those that ride), AT THE TABLE's OWN STEP OF THE OPEN SETS ·
  bPubP: what every other open public item says beside its Bool · bHeld, bShown, bNoColl: the
  samples, the leaves, no collision ride, at the tenants whose pin is open IN FRONT.

Limits. NO FIELD IS SHOWN AT ANY FILLING. The ties fFree, fFresh, fLive are asked BOTH WAYS.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayAtTable
import Johnson.Desc.First.Look.K3CallsKeeps
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3ShapeBehind
import Johnson.Desc.First.BookFit
import Johnson.Desc.Sound.PromiseRidesQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open OnBytes.PscRun
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3 (sizedB freeB k3OnIn k3OnOut)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn shapeAt bookAt pubHeld pubOfItems segRow quietRow sameStand bookFit bookAt_step shift
  pubStep pubRowM stepOpen)

/-- The public items that this file pays behind the block. -/
def paidCalls (m pc : ℕ) : List Pub :=
  [.lookOut m pc, .ledger m, .freeAbove m, .linkFresh m, .left m, liveItem m]

/-- The row of the lookup on the calls closes and opens no class of rows and no pin: at every sort
of segment, the head's too (there the piece is 3). -/
theorem calls_quiet {links : List ModelPart} {p : Desc.Place} {m : ℕ} {sub : ModelPart}
    (hl : p.link = some m) (hs : links[m]? = some sub) (hpc : p.piece = 2 + shift sub) :
    quietRow (Desc.First.rowOf links p) = true := by
  have e : Desc.First.rowOf links p = segRow sub m (2 + shift sub) := by
    unfold Desc.First.rowOf
    simp only [hl, hs, hpc]
  rw [e]
  cases sub <;> rfl

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (x : Desc.First.Look.Place)
  (D : Desc.First.Look.Sent) (set : Params.Setting) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Desc.Place) (pi : P)
  (k m pc : ℕ) (arrs : Array (Nat × String)) (p p' : Desc.Place) (told : List (List Desc.Oracle))
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace set false x
local notation "theO" => Option.getD ((openSets links ps (start links))[k]?) []
local notation "theQ" => Option.getD ((pubSets (Meaning.more Mg) links ps)[k]?) []
local notation "onK" => onQ (Fr := Fr) N Mg links ps (fun s => (pi, s)) k

/-- **The parts of the promise behind.** -/
structure BehindParts : Prop where
  here : ps[k]? = some p
  next : ps[k + 1]? = some p'
  quiet : quietRow (Desc.First.rowOf links p) = true
  stand : sameStand links p p' = true
  fit : bookFit N ps told = true
  tells : told[k]? = some []
  askIn : Pub.lookIn m pc ∈ theQ
  askFree : Pub.freeAbove m ∈ theQ
  askFresh : Pub.linkFresh m ∈ theQ
  askLive : liveItem m ∈ theQ
  pubIn : ∀ s, Mg.pub (.lookIn m pc) (pi, s) = true → k3OnIn theP s = true
  fOut : ∀ s, k3OnOut theP s = true → Mg.pub (.lookOut m pc) (pi, s) = true
  fLedger : ∀ s, (s.fork?.any sizedB) = true → Mg.pub (.ledger m) (pi, s) = true
  fFree : ∀ s, Mg.pub (.freeAbove m) (pi, s) = true ↔ freeAboveAtB (theP).ns s = true
  fFresh : ∀ s, Mg.pub (.linkFresh m) (pi, s) = true ↔ linkFreshB arrs s = true
  fLive : ∀ s, Mg.pub (liveItem m) (pi, s) = true ↔ LiveIs D s
  fLeft : ∀ s, Mg.pub (.left m) (pi, s) = true
  fLeftP : ∀ s, k3LeftItem theP s → Mg.pubP (.left m) (pi, s)
  bOrder : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 → Mg.inOrder (pi, a.1) = true → Mg.inOrder (pi, b.1) = true
  bPub : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 →
    ∀ q ∈ pubStep theQ (pubRowM Mg.more links p) ++
        pubOfItems (stepOpen theO (Desc.First.rowOf links p)),
      q ∉ paidCalls m pc → Mg.pub q (pi, b.1) = true
  bPubP : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 → ∀ q ∈ pubStep theQ (pubRowM Mg.more links p), q ≠ .left m →
      Mg.pubP q (pi, b.1)
  bHeld : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 → ∀ t ∈ sampledIn N theO,
      Mg.held t.1 t.2 (pi, a.1) = true → Mg.held t.1 t.2 (pi, b.1) = true
  bShown : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 → ∀ t ∈ sampledIn N theO,
      Mg.shown t.1 t.2 (strsOf Fr a.2) → Mg.shown t.1 t.2 (strsOf Fr b.2)
  bNoColl : ∀ a b : Desc.First.S × Fr.E.Str, onK a → a.1.failed = none → Yes a b →
    SameBut a.1 b.1 → ∀ t ∈ sampledIn N theO,
      Mg.noColl t.1 t.2 (pi, a.1) (strsOf Fr a.2) → Mg.noColl t.1 t.2 (pi, b.1) (strsOf Fr b.2)

variable {x D set N Mg links ps pi k m pc arrs p p' told Yes}

/-- **THE FIELD "behind", FROM ITS PARTS**: one call of the table's rule for a quiet row.
hY: a yes (in the sense of the letter Yes) is a yes of K3.block's decide at the place's parameters,
at rounds whose words are below the prime. -/
theorem calls_behind (claim : Aff → Cl) (hs : (theP).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide a.1 rs
          cols = .ok c.1)
    (B : BehindParts (Fr := Fr) x D set N Mg links ps pi k m pc arrs p p' told Yes)
    (a b : Desc.First.S × Fr.E.Str) (ha : onK a) (hu : a.1.failed = none) (hy : Yes a b)
    (hsb : SameBut a.1 b.1) (hout : k3OnOut theP b.1 = true)
    (hdec : Mg.decodes (pi, b.1) (strsOf Fr b.2)) :
    onQ N Mg links ps (fun s => (pi, s)) (k + 1) b := by
  obtain ⟨piece, laid, before, guests, rs, cols, hw, hd⟩ := hY a b hy
  obtain ⟨hq, -⟩ := onQ_arm ha hu
  have hIn : k3OnIn theP a.1 = true := B.pubIn _ (hq _ B.askIn)
  obtain ⟨F, F', g, hF, -, -, hF', -, L, -⟩ :=
    k3_calls_leaves claim piece laid before theP guests hs a.1 b.1 rs cols hw hd hIn
  -- the book-keeping's first Bool in front
  have hsh : shapeAt links (some p) a.1 = true := by
    obtain ⟨-, hm | ⟨h1, -⟩⟩ := ha
    · exact absurd hu hm
    · simp only [Bool.and_eq_true] at h1
      have h2 := h1.1.1.1.1.1
      rw [B.here] at h2
      exact h2
  have hk : k < ps.length := (List.getElem?_eq_some_iff.1 B.here).1
  -- what the item "left" keeps of the ledger in front
  have hQ : LeftQ (theP).ns F := by
    obtain ⟨F1, hF1, hz, -, -⟩ := k3OnIn_free hs hIn
    obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
    have f0 := (B.fFree _).1 (hq _ B.askFree)
    unfold freeAboveAtB at f0
    simp only [Bool.and_eq_true] at f0
    have f1 := f0.2
    rw [hF] at f1
    simp only [Option.any_some, beq_iff_eq] at f1
    have f2 := f0.1
    unfold freeAboveB at f2
    rw [hF] at f2
    simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at f2
    refine ⟨hz, f1, fun j hj hlt => ?_⟩
    have q := f2 (j - F.next) (by omega)
    rw [show F.next + (j - F.next) = j by omega] at q
    exact q
  -- the six
  have p2 : Mg.pub (.ledger m) (pi, b.1) = true :=
    B.fLedger _ (k3_calls_ledger claim piece laid before theP guests hs a.1 b.1 rs cols hw hd hIn)
  have p3 : Mg.pub (.freeAbove m) (pi, b.1) = true := by
    have f0 := (B.fFree _).1 (hq _ B.askFree)
    unfold freeAboveAtB at f0
    simp only [Bool.and_eq_true] at f0
    refine (B.fFree _).2 ?_
    unfold freeAboveAtB
    simp only [Bool.and_eq_true]
    refine ⟨k3_calls_freeAbove claim piece laid before theP guests hs a.1 b.1 rs cols hw hd hIn
      f0.1, ?_⟩
    have f1 := f0.2
    rw [hF] at f1
    rw [hF']
    simp only [Option.any_some] at f1 ⊢
    rw [L.padLeft.rest.2.1]
    exact f1
  have p4 : Mg.pub (.linkFresh m) (pi, b.1) = true := by
    have f0 := (B.fFresh _).1 (hq _ B.askFresh)
    refine (B.fFresh _).2 ?_
    unfold linkFreshB at f0 ⊢
    rw [k3_calls_unheard claim piece laid before theP guests a.1 b.1 rs cols hd,
      k3_calls_linkSame claim piece laid before theP guests a.1 b.1 rs cols hd]
    exact f0
  have p6 : Mg.pub (liveItem m) (pi, b.1) = true :=
    (B.fLive _).2 (liveIs_sameBut hsb ((B.fLive _).1 (hq _ B.askLive)))
  refine onQ_step_quiet N Mg links ps (fun s => (pi, s)) k p B.here B.quiet a b ha
    (fun hm => absurd hu hm) (fun _ => hdec) ?_ (by rw [hsb.st]) (by rw [hsb.book])
    (B.bOrder a b ha hu hy hsb) ?_ ?_ ?_ (B.bHeld a b ha hu hy hsb) (B.bShown a b ha hu hy hsb)
    (B.bNoColl a b ha hu hy hsb)
  · intro _
    rw [B.next]
    exact sameBut_shapeAt hsb B.stand hsh
  · intro _ _
    unfold pubHeld
    rw [List.all_eq_true]
    intro q hqm
    by_cases hp : q ∈ paidCalls m pc
    · unfold paidCalls at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact B.fOut _ hout
      · exact p2
      · exact p3
      · exact p4
      · exact B.fLeft _
      · exact p6
    · exact B.bPub a b ha hu hy hsb q hqm hp
  · intro _ hb
    exact bookAt_step N ps told B.fit k hk B.tells a.1 b.1 hsb.book (by rw [hsb.st]) hb
  · intro _ _ q hqm
    by_cases hl : q = .left m
    · rw [hl]
      exact B.fLeftP _
        (k3_calls_leftItem claim piece laid before theP guests a.1 b.1 rs cols hs hw hd hF hQ)
    · exact B.bPubP a b ha hu hy hsb q hqm hl

/-! ## That it IS the field: Lean lays it in the field's place -/

/-- At attention: the structure with calls_behind laid as its field "behind". -/
theorem att_behind_fits {Xi : Type} (G : Desc.FileDescription Xi) (A : Attention.Shape) (tl : HTailF2)
    (rad : OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (claim : Aff → Cl) (hs : (theP).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide a.1 rs
          cols = .ok c.1)
    (B : BehindParts (Fr := Fr) x D set N Mg links ps pi k m 2 arrs p p' told Yes)
    (T : AttAtTable (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m Yes) :
    AttAtTable (Fr := Fr) G x A tl D rad set seatT arr smp claim N Mg links ps pi k m Yes :=
  { T with behind := calls_behind claim hs hY B }

/-- At the layers: the like. -/
theorem lay_behind_fits {Xi : Type} (G : Desc.FileDescription Xi) (q : LayPub) (tl : HTailF2)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
    (claim : Aff → Cl) (hs : (theP).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide a.1 rs
          cols = .ok c.1)
    (B : BehindParts (Fr := Fr) x D set N Mg links ps pi k m 2 arrs p p' told Yes)
    (T : LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N
      Mg links ps pi k m Yes) :
    LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW claim N
      Mg links ps pi k m Yes :=
  { T with behind := calls_behind claim hs hY B }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_behind
#print axioms VerifiableInference.OnPublicFiles.att_behind_fits
#print axioms VerifiableInference.OnPublicFiles.lay_behind_fits
