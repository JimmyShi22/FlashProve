-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RidersLight.lean: "WHAT RIDES" GOES BACK OVER A STEP THAT MAY TURN THE
GROUPS, THE LEDGERS AND THE MARK "SPENT AS A MASK": AT THE COMPOSED MEANING (mgAll 𝔇 Mg), FOR THE
SORTS OF ITEM THAT READ NONE OF THESE, AND FOR "wo", WHICH READS ONE LEDGER, UNDER A PREMISE OF ITS
OWN. AND SO AT K10's ACCEPTING STEP: THE PREMISE hs
OF k10_back_of_sides (Johnson/Desc/First/Close/Law/KindK10Riders.lean), to the letter, from named
premises. Theorems with their proofs.

Whence. The rule is holds_back_push (Link/Law/FifthTieEq.lean) with its
reading ReadW made lighter: K10's step empties the group's list of rows and marks the mask's
message, so ReadW's fields "classes" and "msgs" do not hold over it; the arms for the sorts below
spend neither. THE ARMS' PROOFS ARE THAT FILE's, line for line; once it stands in a build with this
file, its rule can call this one.

  ReadK s t        what these sorts read of the state in front (s) and behind (t): the book · the
                   code tables · the number of messages · each message's shape · the rows on the
                   weights
  lightRider       constr · pin · pinKept · pinI · pinV · pinW · pile · wo
  holds_back_light **every such rider goes back over a relation that gives ReadK**; "wo" under a
                   premise of its own (it reads a ledger)
  rows_putRec      putRec leaves the rows on the weights
  readK_k10        **K10's accepting step (K10Step) gives ReadK**
  IndexFree s      the index masks' message is a member of no group
  rowAt_of_ledger, k10_rowAt, wo_back_k10   **"wo" goes back over K10's step from an IndexFree
                   state**: its reader reads, of the statement, that one message's ledger, and K10
                   closes the ledgers of the group's members alone (k10_ledger)
  R10 F base       the relation: the public part is the same · K10Step · the strings stand behind a
                   stage at that base · the state in front is IndexFree
  k10_ride         **hs, TO THE LETTER**

"wo" is needed: it rides at K10's places of the 13 layers' and head's
segments (by the kernel: RidersAtK10.lean): without it the premise on the riders cannot be met.

Limits. LEFT AS PREMISES, EACH BY NAME: hstep (K10CondAt's field "step") · hidx (under the promise
in front and Rch the state is IndexFree) · Read3 𝔇 (· < base)
(R10 F base): the three readers 𝔇.H.req, 𝔇.decT, 𝔇.smp answer alike in front and behind · HeadOpen ·
on every rider: it is of a sort in lightRider, it is not the digits' part, its pins' trees lie below
base. 𝔇 IS A LETTER HERE. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameItemsOpen
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Desc.First.Close.Law.RidesBehind
import Johnson.Desc.First.Close.Law.T2AtPiece
import Johnson.Desc.First.Close.Law.EPubAtK10
import Johnson.Desc.Sound.BordersSidesOnR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start)
open VerifiableInference.Desc.First.Close (K10Step Behind)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook_same)
open VerifiableInference.OnPublicFiles (headLink)
open Johnson.Desc.First.Walk.Tied
open _root_.Run (ckP)

/-- **What the light riders' sentences read of the state in front (s) and behind (t).** -/
structure ReadK (s t : S) : Prop where
  book : t.book = s.book
  codes : t.st.codes = s.st.codes
  size : t.st.oracles.size = s.st.oracles.size
  shape : ∀ o : ℕ, (t.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape) =
    (s.st.oracles[o]?).map fun a : OnBytes.Oracle => a.shape
  rows : ∀ r ∈ s.rows, r ∈ t.rows

/-- The sorts of item of which the rule speaks. -/
def lightRider : Item → Bool
  | .constr _ _ | .pin _ _ | .pinKept _ | .pinI | .pinV | .pinW | .pile | .wo _ => true
  | _ => false

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **EVERY SUCH RIDER GOES BACK.** -/
theorem holds_back_light (N : Numbers) (Op : Item → Prop) (low : ℕ → Prop)
    (R : P × S → Strs → P × S → Strs → Prop)
    (hcell : ∀ a y b y', R a y b y' → ∀ x, y'.cell x = y.cell x)
    (hcol : ∀ a y b y', R a y b y' → ∀ j, low j → ∀ x, y'.col j x = y.col j x)
    (hst : ∀ a y b y', R a y b y' → ReadK a.2 b.2) (h3 : Read3 𝔇 low R)
    (hH : HeadOpen 𝔇 Op R)
    (hw : ∀ m, Op (.wo m) → GoesBack R (First.FillP1.woAt 𝔇.d1 𝔇.rw13 m))
    (hO : ∀ i, Op i → lightRider i = true ∧ notOwn ownDigits i ∧ lowItem N low i) :
    ∀ i, Op i → GoesBack R (i.holds N (mgAll 𝔇 Mg)) := by
  have pinB : ∀ j t, low j → GoesBack R ((mgAll 𝔇 Mg).pin j t) := by
    intro j t hj
    rw [mgAll_pin]
    intro a y b y' w h hp
    have hp' := pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms j t b y' y w
      (fun x => (hcol a y b y' h j hj x).symm) hp
    refine ⟨hp'.1, fun x hx hs => ?_⟩
    obtain ⟨z, hz, h2, h4⟩ := hp'.2 x hx hs
    have hs' : x.1.seat x.2 = (j, t) := hs
    refine ⟨z, ?_, h2, h4⟩
    show 𝔇.smp a x.1 x.2 = some z
    rw [h3.smp a y b y' h x hx (by rw [hs']; exact hj)]
    exact hz
  intro i hi
  obtain ⟨hp, ho, hl⟩ := hO i hi
  cases i with
  | constr m p =>
    have ho' : (p == .lookDigits) = false := ho
    have h1 : p ≠ .lookDigits := by
      intro e
      subst e
      simp at ho'
    have hdec : ∀ a y b y', R a y b y' →
        (oneDec 𝔇.decT 𝔇.H).dec a y = (oneDec 𝔇.decT 𝔇.H).dec b y' := by
      intro a y b y' h
      show 𝔇.decT y.cell a = 𝔇.decT y'.cell b
      rw [show y'.cell = y.cell from funext (hcell a y b y' h)]
      exact h3.dec a y b y' h _
    show GoesBack R ((mgAll 𝔇 Mg).constr m p)
    rw [mgAll_constr]
    by_cases hm : m = headLink X
    · subst hm
      exact constrQAt_back_any (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart _ p
        h1 R (fun a y b y' h => h3.req a y b y' h) hdec (hH p hi)
    · exact constrQAt_back (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p h1
        hm R (fun a y b y' h => h3.req a y b y' h) hdec
  | pin m t => exact fun a y b y' w hr h x hx => pinB x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinKept m => exact fun a y b y' w hr h x hx => pinB x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinI => exact pinB _ _ hl
  | pinV => exact pinB _ _ hl
  | pinW =>
    show GoesBack R (mgAll 𝔇 Mg).pinW
    rw [mgAll_pinW]
    intro a y b y' w h hq
    show 𝔇.decT y.cell a = some w.cells
    rw [h3.dec a y b y' h, ← show y'.cell = y.cell from funext (hcell a y b y' h)]
    exact hq
  | pile =>
    show GoesBack R (mgAll 𝔇 Mg).pile
    rw [mgAll_pile]
    intro a y b y' w h hq
    have hS := hst a y b y' h
    have hq' : RowsTrue (𝔇.rw13 b) b.2 w := hq
    have e : 𝔇.rw13 b w = 𝔇.rw13 a w := rwBook_same 𝔇.arr 𝔇.mat13 a b hS.book hS.codes hS.shape w
    show RowsTrue (𝔇.rw13 a) a.2 w
    intro r hr
    have h1 := hq' r (hS.rows r hr)
    rw [e] at h1
    exact h1
  | wo m =>
    show GoesBack R ((mgAll 𝔇 Mg).wo m)
    rw [mgAll_wo]
    exact hw m hi
  | _ => cases hp

end

/-! ## K10's accepting step -/

/-- Writing the live copy leaves the rows on the weights. -/
theorem rows_putLive (s : S) (c : ChainCheck) : (s.putLive c).rows = s.rows := by
  unfold S.putLive
  cases h : s.link? with
  | none => rfl
  | some L =>
    unfold S.putLink S.rows
    cases hh : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
    | _ => first | rfl | simp [hh]

/-- putRec leaves the rows on the weights. -/
theorem rows_putRec (s : S) (r : First.Close.Rec) : (putRec s r).rows = s.rows :=
  rows_putLive s { s.live with frame := r.frame }

/-- **K10's accepting step gives the light reading.** -/
theorem readK_k10 {s t : S} (h : K10Step s t) : ReadK s t := by
  obtain ⟨es, rs, x, hx, rfl⟩ := h
  obtain ⟨h1, h2, h3, _, _, h6, _⟩ := First.Close.k10_rides s es rs x hx
  exact ⟨h6, h1, h2, h3, fun r hr => by rw [rows_putRec]; exact hr⟩

/-- The index masks' message is a member of no group. -/
def IndexFree (s : S) : Prop := ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members

/-- **The reader of the pending claim on the weights reads, of the statement, one ledger.** (The
step "hrow" inside hasRow_of_ledger, Close/Law/EPubAtK10.lean, lifted.) -/
theorem rowAt_of_ledger {s s' : S} (ho : s'.out = s.out)
    (hl : Johnson.Desc.First.Walk.Law.leftOf s' = Johnson.Desc.First.Walk.Law.leftOf s)
    (hd : (s'.st.oracles[s.out.indexMasks]?).bind (·.ledger) =
      (s.st.oracles[s.out.indexMasks]?).bind (·.ledger))
    (lay : WsLay) (n : ℕ) (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.rowAt lay n lin s' =
      Johnson.Desc.First.Walk.Law.rowAt lay n lin s := by
  have key : ∀ (A B : Array OnBytes.Oracle) (i : ℕ) (w : WsForkOut) (r : TensorRow),
      (B[i]?).bind (·.ledger) = (A[i]?).bind (·.ledger) →
      (∃ os, First.Pend.pendingRowO lay i w n lin A = .ok (r, os)) →
      ∃ os, First.Pend.pendingRowO lay i w n lin B = .ok (r, os) := by
    intro A B i w r hAB ⟨os, hos⟩
    obtain ⟨c1, c2, c3, c4, fi, la, c5, c6, c7, c8, c9, Ga, c10, g, c11, l, c12, c, l', c13, c14,
      _⟩ := (First.Pend.pendingRowO_iff lay i w n lin A os r).1 hos
    exact ⟨_, (First.Pend.pendingRowO_iff lay i w n lin B _ r).2 ⟨c1, c2, c3, c4, fi, la, c5, c6,
      c7, c8, c9, Ga, c10, g, c11, l, by rw [hAB]; exact c12, c, l', c13, c14, rfl⟩⟩
  apply Option.ext
  intro r
  unfold Johnson.Desc.First.Walk.Law.rowAt
  rw [Johnson.Desc.First.Walk.Law.rowBy_some, Johnson.Desc.First.Walk.Law.rowBy_some, hl, ho]
  constructor
  · rintro ⟨w, os, hw, hp⟩
    obtain ⟨os', hp'⟩ := key _ _ _ w r hd.symm ⟨os, hp⟩
    exact ⟨w, os', hw, hp'⟩
  · rintro ⟨w, os, hw, hp⟩
    obtain ⟨os', hp'⟩ := key _ _ _ w r hd ⟨os, hp⟩
    exact ⟨w, os', hw, hp'⟩

/-- **Over K10's step that reader answers alike**, from a state whose index masks' message is a
member of no group. -/
theorem k10_rowAt {s t : S} (h : K10Step s t) (hI : IndexFree s) (lay : WsLay) (n : ℕ)
    (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.rowAt lay n lin t =
      Johnson.Desc.First.Walk.Law.rowAt lay n lin s := by
  obtain ⟨es, rs, x, hx, rfl⟩ := h
  obtain ⟨hl, -, ho⟩ := First.Close.k10_ledger s es rs x hx _ hI
  exact rowAt_of_ledger ho (First.Close.leftOf_putRec s _) hl lay n lin

/-- The relation over K10's piece. -/
def R10 {P : Type} (F : Frame) (base : ℕ) : P × S → Strs → P × S → Strs → Prop :=
  fun a y b y' => b.1 = a.1 ∧ K10Step a.2 b.2 ∧ Behind F base y y' ∧ IndexFree a.2

theorem behind_stays {F : Frame} {base : ℕ} {y y' : Strs} (h : Behind F base y y') :
    Stays base y y' := by
  obtain ⟨ds, u, τ, rfl, rfl⟩ := h
  exact stays_behind (ckP .two) F base ds u τ

section
variable {Xi Pz Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi Pz Tok rows cols nR X)
  (Mg : Meaning Pz (Wit (CellsQ rows cols) Tok MsgT)) {F : Frame}

/-- **"wo" goes back over K10's accepting step.** -/
theorem wo_back_k10 (base m : ℕ) :
    GoesBack (R10 (P := Pz) F base) (First.FillP1.woAt 𝔇.d1 𝔇.rw13 m) := by
  intro a y b y' w hr h
  obtain ⟨p, s⟩ := a
  obtain ⟨p', t⟩ := b
  obtain ⟨e, hq, -, hI⟩ := hr
  obtain rfl : p' = p := e
  have hS := readK_k10 hq
  unfold First.FillP1.woAt at h ⊢
  intro r hrow
  have e2 : 𝔇.rw13 (p', t) w = 𝔇.rw13 (p', s) w :=
    rwBook_same 𝔇.arr 𝔇.mat13 (p', s) (p', t) hS.book hS.codes hS.shape w
  have h1 := h r (by
    show Johnson.Desc.First.Walk.Law.rowAt _ _ _ t = some r
    rw [k10_rowAt hq hI]
    exact hrow)
  rw [e2] at h1
  exact h1

/-- **e₁'s ROW 102: hs OF k10_back_of_sides, TO THE LETTER, AT THE COMPOSED MEANING.** -/
theorem k10_ride (Nu : Numbers) (links : List ModelPart) (ps : List Place)
    (Rch : ℕ → (Pz × S) × F.E.Str → Prop) (k base : ℕ)
    (q₀ : Piece (ckP .two) F (Pz × S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, q₀.ior.red.out a τ = some b →
      b.1.1 = a.1.1 ∧ K10Step a.1.2 b.1.2 ∧ Behind F base (strsOf F a.2) (strsOf F b.2))
    (hidx : ∀ a, onQ Nu (mgAll 𝔇 Mg) links ps (fun a => a) k a → Rch k a → IndexFree a.1.2)
    (h3 : Read3 𝔇 (· < base) (R10 F base))
    (hH : HeadOpen 𝔇 (fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i ∧
      ¬ insQ links ps k i) (R10 F base))
    (hO : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i →
      lightRider i = true ∧ notOwn ownDigits i ∧ lowItem Nu (· < base) i) :
    ∀ a τ b w i, onQ Nu (mgAll 𝔇 Mg) links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q₀.ior.red.out a τ = some b → onQ Nu (mgAll 𝔇 Mg) links ps (fun a => a) (k + 1) b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nu (mgAll 𝔇 Mg) (fun a => a) i b w → meansQ Nu (mgAll 𝔇 Mg) (fun a => a) i a w := by
  intro a τ b w i hon hrch _ hb _ ho hn hm
  obtain ⟨s1, s2, s3⟩ := hstep a τ b hb
  have hr : R10 F base a.1 (strsOf F a.2) b.1 (strsOf F b.2) := ⟨s1, s2, s3, hidx a hon hrch⟩
  exact holds_back_light 𝔇 Mg Nu _ (· < base) (R10 F base)
    (fun _ _ _ _ h x => (behind_stays h.2.2.1).1 x)
    (fun _ _ _ _ h j hj x => (behind_stays h.2.2.1).2 j x hj)
    (fun _ _ _ _ h => readK_k10 h.2.1) h3 hH (fun m _ => wo_back_k10 𝔇 base m)
    (fun i hi => hO i hi.1 hi.2) i ⟨ho, hn⟩
    a.1 (strsOf F a.2) b.1 (strsOf F b.2) w hr hm

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.holds_back_light
#print axioms VerifiableInference.Desc.LinkJoin.rows_putRec
#print axioms VerifiableInference.Desc.LinkJoin.readK_k10
#print axioms VerifiableInference.Desc.LinkJoin.wo_back_k10
#print axioms VerifiableInference.Desc.LinkJoin.k10_ride
