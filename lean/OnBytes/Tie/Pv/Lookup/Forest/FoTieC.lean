-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieC.lean.
The sub-proofs' lookup: what the byte-level routines hand on is what the typed verifier puts out.

Neither side tests an equation at a lookup: each hands on linear claims. So the tie between the
byte-level verifier and the typed one is, at this block, an equation of what is handed on. This
file states it as one closed proposition, at the reading Reading.gl in the field Cb.Gl.E.

Main names:
  `nuOf mk pl μ₀`: the lookup's places read in the caller's entries μ₀; a place that is no entry
    reads 0.
  `TieRows`: in every later state, under every reading of the places: the values of Heard.rows are
    the first values of the list Fo.claimsOf: each row's form less its target. No run, no caller.
  `TiePlanes`: a run of Forest.planeClaims that returns, from a later state whose arrays have their
    sizes (Sized) and on routines bit and pin that change no state, changes no context, leaves a
    later state, and in every state later than that the values of its three forms are
    Fo.claimLeaves, Fo.claimBits and Cb.Fo.Pin.countK, the caller's forms entering by their values.
  `TieJoin`: for one key form a call, in every later state: the value of the form that Forest.join
    returns (Fo.joinForm) is Fo.claimJoin, the caller's key forms entering by their values.
  `portForms g planes KF`: the byte-level forms in the order rows, planes, join. The callers' own
    orders differ.
  `CallerOk`: what is asked of the caller's arguments at the entries μ₀: its routines bit and pin
    change no state; in each of the planes' columns the forms that they give are worth the
    column's sum under the weights of zb0, of zb1 and under the powers of 2; it gives one key form
    a call, worth the call's key vector at its point.
  `TieIff`: where planes is what a run of Forest.planeClaims as in TiePlanes returned, in every
    state later than the one that it left, under CallerOk: all values of portForms are 0 if and only
    if the typed lookup's out-claim holds at what the typed verifier has put out.
  `HCtie`: for every run of Forest.pad on a view that returns: ShapeOf, PadLeft; it took rounds rv
    off the view; HeardIs, TieRows, TiePlanes, TieJoin at rv read by Reading.gl; and if no 0 was
    drawn where a further variable's challenge stands (Fo.YNonZero), then for every statement:
    some typed transcript, read as plain data, is rv read; the typed verifier is knowledge sound
    from the lookup's in-claim to its out-claim (TWhole.KnowAt, with the errors of Cb.Fo.forB's
    own field e and the identity on the further witness as extractor); and on EVERY typed
    transcript with that reading the typed verifier puts out an x whose state is the caller's with
    the shift, with TieIff.
Under (premises of HCtie, all on public data or on the states before the run): the slots' arrays
have their sizes (Sized); a view, no message open (Clean); 5 ≤ lm ≤ kT + 5; the caller's layout L
lays mask entry s of the lookup at mk (F.next + s) and the cells by pl.
Limits: YNonZero is a premise on the view: the byte-level routine does not test it; it is the
strict reader's rule for that draw. CallerOk is the caller's to show. TiePlanes, TieJoin and TieIff
speak of Forest.planeClaims and of the form of Forest.join. A caller that makes its claims on the
planes or its claim on the keys by hand, or makes no claim on the keys but starts a sumcheck from
that form, is served by HeardIs and Fo.hcClaims, not by these three. Where the claims stand in the
sub-proof's own numbering, and that the caller adds them all, is not said here. Nothing is said of
a run that does not return. That the errors of Cb.Fo.forB are small is not said here.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoMeetPlan
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Port.FoShape
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Cb.Fo.PlaneClaims OnBytes OnBytes.Model OnBytes.PscRun

/-- The reading in the library's field. -/
abbrev gl : Model.Reading Cb.Gl.E := Model.Reading.gl

/-- The world in the state H in which mask entry j is what ν reads at its place. -/
abbrev wOf (H : Fork) (ν : Pl → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) : Model.World Cb.Gl.E :=
  H.worldOf gl (fun j => ν (.mask j)) entry

/-- The claims on mask entries alone. -/
def TieRows (g : Forest.Heard) (F' : Fork) (lm jLK : ℕ) (rs : Rounds Cb.Gl.E) : Prop :=
  ∀ H, Later F' H → ∀ (ν : Pl → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
    (g.rows.toList.map fun f => f.value gl (wOf H ν entry)) =
      (endsOf g.shape lm jLK rs).rows.map (rowRes ν)

/-- The three claims on the planes. -/
def TiePlanes (g : Forest.Heard) (F' : Fork) (lm jLK : ℕ) (rs : Rounds Cb.Gl.E) : Prop :=
  ∀ (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff) (F1 G : Fork) (c1 c2 : Ctx)
    (planes : Array Aff), (∀ e col, Quiet (bit e col)) → (∀ col, Quiet (pin col)) →
    Later F' F1 → Sized F1 → Forest.planeClaims g lm bit pin F1 c1 = .ok ((planes, G), c2) →
    c2 = c1 ∧ Later F1 G ∧ Sized G ∧ G.next = F1.next ∧
      ∀ H, Later G H → ∀ (ν : Pl → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
        (planes.toList.map fun f => f.value gl (wOf H ν entry)) =
          [claimLeaves g.shape lm jLK rs ν fun col =>
              (got (bit 0 col) F1 c1).value gl (wOf H ν entry),
            claimBits g.shape lm jLK rs ν fun col =>
              (got (bit 1 col) F1 c1).value gl (wOf H ν entry),
            countK g.shape lm fun col => (got (pin col) F1 c1).value gl (wOf H ν entry)]

/-- The claim on the key vectors. -/
def TieJoin (g : Forest.Heard) (F' : Fork) (lm jLK : ℕ) (rs : Rounds Cb.Gl.E) : Prop :=
  ∀ (KF : Array Aff), KF.size = g.shape.NC →
    ∀ H, Later F' H → ∀ (ν : Pl → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
      (joinForm g KF).value gl (wOf H ν entry) =
        claimJoin g.shape lm jLK rs ν fun k =>
          (KF.getD k (Aff.ofConst zeroE)).value gl (wOf H ν entry)

/-- The byte-level forms of one lookup's claims, in the order rows, planes, join. -/
def portForms (g : Forest.Heard) (planes KF : Array Aff) : List Aff :=
  g.rows.toList ++ planes.toList ++ [joinForm g KF]

/-- The number of columns of the planes' matrix. -/
def nCols (h : FoNums.Sh) (lm : ℕ) : ℕ := h.NC * 2 ^ (h.kT + 5 - lm)

section
variable {St₀ J₀ : Type}

/-- The lookup's places, read in the caller's entries. -/
def nuOf (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (μ₀ : J₀ → Cb.Gl.E) : Pl → Cb.Gl.E :=
  fun p => zext μ₀ (placeOf mk pl p)

/-- What is asked of the caller's arguments, in the world W. ν: the reading of the lookup's places;
Kv c i: key number i of call c at the caller's entries. -/
structure CallerOk (g : Forest.Heard) (lm : ℕ) (En : Ends Cb.Gl.E) (ν : Pl → Cb.Gl.E)
    (W : Model.World Cb.Gl.E) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff) (F1 : Fork) (c1 : Ctx)
    (KF : Array Aff) (Kv : ℕ → ℕ → Cb.Gl.E) : Prop where
  quietB : ∀ e col, Quiet (bit e col)
  quietP : ∀ col, Quiet (pin col)
  col0 : ∀ col < nCols g.shape lm,
    (got (bit 0 col) F1 c1).value gl W = colsK g.shape lm En.zb0 ν col
  col1 : ∀ col < nCols g.shape lm,
    (got (bit 1 col) F1 c1).value gl W = colsK g.shape lm En.zb1 ν col
  pinC : ∀ col < nCols g.shape lm, (got (pin col) F1 c1).value gl W = pinColK lm ν col
  nKF : KF.size = g.shape.NC
  kf : ∀ k < g.shape.NC,
    (KF.getD k (Aff.ofConst zeroE)).value gl W = extL (Kv k) (En.zk.getD k [])

variable [Fintype J₀] [DecidableEq J₀]

/-- All byte-level claims of the lookup vanish if and only if the typed out-claim holds. -/
def TieIff (g : Forest.Heard) (F' : Fork) (lm jLK : ℕ) (rs : Rounds Cb.Gl.E)
    (L : Lay Cb.Gl.E St₀ J₀) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (st : St₀)
    (x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) : Prop :=
  ∀ (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff) (KF : Array Aff) (F1 G H : Fork) (c1 c2 : Ctx)
    (planes : Array Aff) (μ₀ : J₀ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
    Later F' F1 → Sized F1 → Forest.planeClaims g lm bit pin F1 c1 = .ok ((planes, G), c2) →
    Later G H →
    CallerOk g lm (endsOf g.shape lm jLK rs) (nuOf mk pl μ₀) (wOf H (nuOf mk pl μ₀) entry) bit pin
      F1 c1 KF (forK Cb.Gl.E L st (zext μ₀)) →
    ((∀ f ∈ portForms g planes KF, f.value gl (wOf H (nuOf mk pl μ₀) entry) = 0) ↔
      (forA Cb.Gl.E g.shape L).lk.out id id x (zext μ₀))

end

/-- What the byte-level routines of a sub-proof's lookup hand on is what the typed verifier puts
out: a closed proposition. -/
def HCtie : Prop :=
  ∀ (calls : Array Call) (pub : Array Nat) (lid lm : ℕ) (F F' : Fork) (c c' : Ctx)
    (g : Forest.Heard) (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (L : Lay Cb.Gl.E St₀ J₀)
    (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    Forest.pad calls pub lid F c = .ok ((g, F'), c') → Sized F → Clean c →
    5 ≤ lm → lm ≤ g.shape.kT + 5 → (∀ s, L.mkS s = mk (F.next + s)) →
    (∀ t k j, k < g.shape.NC → L.bc t k j =
      pl (FoNums.cellRC g.shape lm (t, k, j)).1 (FoNums.cellRC g.shape lm (t, k, j)).2) →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    ∃ rv : List Fmt.RoundView, Took c rv c' ∧
      HeardIs gl g F' (endsOf g.shape lm F.next (rv.map (rdRV gl))) ∧
      TieRows g F' lm F.next (rv.map (rdRV gl)) ∧ TiePlanes g F' lm F.next (rv.map (rdRV gl)) ∧
      TieJoin g F' lm F.next (rv.map (rdRV gl)) ∧
      (YNonZero g.shape (rv.map (rdRV gl)) →
        ∀ (Ex : ExtSpec) (a : St₀ × Ex.Str),
          (∃ τ : Tr (forB Cb.Gl.E g.shape L V₀ V₀C (Ex := Ex)).R.shape,
            forFl g.shape L Ex τ = rv.map (rdRV gl)) ∧
          (∀ (Kc M Wp : Type) (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E),
            KnowAt (forB Cb.Gl.E g.shape L V₀ V₀C (Ex := Ex)).R
              (forIn Cb.Gl.E g.shape L R0 msg₀) (forOut Cb.Gl.E g.shape L R0 msg₀)
              (fun _ _ _ wp => wp) (forB Cb.Gl.E g.shape L V₀ V₀C (Ex := Ex)).e) ∧
          ∀ τ : Tr (forB Cb.Gl.E g.shape L V₀ V₀C (Ex := Ex)).R.shape,
            forFl g.shape L Ex τ = rv.map (rdRV gl) →
            ∃ x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀),
              (forB Cb.Gl.E g.shape L V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
              x.1 = (a.1, (endsOf g.shape lm F.next (rv.map (rdRV gl))).theta) ∧
              TieIff g F' lm F.next (rv.map (rdRV gl)) L mk pl a.1 x)

end Fo
