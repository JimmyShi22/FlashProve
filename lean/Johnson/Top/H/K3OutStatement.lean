-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutStatement.lean: the kind "lookup" (K3): A STATEMENT, NOT PROVED HERE: where the
kind's decide says yes at a written transcript's rounds, its three runs of claims say yes at later
records, and every claim's form is worth 0 at a ledger behind the runs, the proved block's out-claim
holds at the statement that the block puts out at that transcript's image. Definitions of type Prop.

Main names:
  `K3HostLaw`: WHAT THE CALLING KIND OWES on the forms that it hands in: each form on a column of
    the planes' matrix is worth that column's combination of the matrix's cells (colsK, at the
    leaves' point and at the bits' point); each form for the counts is worth pinColK; call c's key
    form is worth the extension of call c's key vector at call c's point. Asked only at the
    columns and calls that the claims read.
  `K3RanAt`: one run of claims said yes at a record at which what was heard still stands and whose
    ledger is a later one than the hearing's, with its sizes.
  `K3ClaimsGiveOut`: the statement, at letters for the kind's functions.

How the world is read. ν p := zext μ₀ (placeOf mk pl p), for entries μ₀ of the proved block's index
set: the mask under slot j is ν (.mask j), cell (row, col) of the planes' matrix is ν (.cell row
col). The claims are judged at H.worldOf Reading.gl (fun j => ν (.mask j)) entry, for a ledger H
later than the three ledgers that the runs leave, and for the entries "entry" of virtual rows at
which the host's law is given.

Limits. Nothing is proved here. A tie with no error term: it says nothing on a cheating prover's
chance. The premises stand at letters: the public tests (ShapeOf) at the proved caller's own shape;
5 ≤ lm ≤ kT + 5; two laws on the layout, with the lookup's first slot the ledger's next free one;
the written rounds meet the block's spec and hold no answers; their words are below the prime; the
ledger in front has its sizes; the host's law. None is shown at a value. That the claims are in fact
worth 0 is what the link's one equation is meant to give; it is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LawClaims
import Johnson.Top.H.K3LawKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- **What the calling kind owes on the forms that it hands in.** h, lm: the shape; the matrix has
2 ^ lm rows. zb0, zb1: the leaves' point and the bits' point. zk c: call c's point. ν: the reading
of the places. Kv c i: key number i of call c. val: the value of a form. bit e col, pin col, keys:
the forms. -/
structure K3HostLaw {K : Type} [CommRing K] (h : FoNums.Sh) (lm : ℕ) (zb0 zb1 : List K)
    (zk : ℕ → List K) (ν : _root_.Fo.Pl → K) (Kv : ℕ → ℕ → K) (val : Aff → K)
    (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff) (keys : Array Aff) : Prop where
  bit0 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (bit 0 col) = colsK h lm zb0 ν col
  bit1 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (bit 1 col) = colsK h lm zb1 ν col
  pin : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (pin col) = pinColK lm ν col
  keys : ∀ c, c < h.NC → val (keys.getD c (Aff.ofConst zeroE)) = extL (Kv c) (zk c)

/-- **One run of claims said yes at a later record.** g, F': what the hearing left. s: the record at
which the run is called. cl: its claims. G: the ledger that it leaves. -/
structure K3RanAt {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (g : Forest.Heard) (F' : Fork) (run : ℕ → S → Except String (List Cl × S)) (s : S)
    (cl : List Cl) (G : Fork) : Prop where
  heard : heard s = some g
  later : ∃ F, fork s = some F ∧ _root_.Fo.Later F' F ∧ OnBytes.PscRun.Sized F
  ran : ∃ n s', run n s = .ok (cl, s') ∧ fork s' = some G

/-- **The kind's yes, its runs' yes and its claims worth 0 give the proved block's out-claim.**
fork, heard, form, decide, objects, planes, join: the kind's functions. calls, pub, lid, lm: the
place's public parameters. bit, pin, keys: the caller's forms at a record. NOT PROVED HERE. -/
def K3ClaimsGiveOut {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (form : Cl → Aff) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S)
    (objects planes join : ℕ → S → Except String (List Cl × S))
    (bit : S → ℕ → ℕ → Aff) (pin : S → ℕ → Aff) (keys : S → Array Aff) : Prop :=
  ∀ (L : List LookupCRCaller) (r : LookupCRCaller), ShapeOf calls pub lid r.c.h →
  5 ≤ lm → lm ≤ r.c.h.kT + 5 →
  ∀ (s s₁ : S) (F : Fork), fork s = some F → OnBytes.PscRun.Sized F →
  ∀ (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀),
    (∀ t, r.c.L.mkS t = mk (F.next + t)) →
    (∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2) →
  ∀ (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF r.c.h)),
    (∀ d ∈ ds, NoAns d.items) →
  ∀ (a : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds))
    (cols : List (List (ℕ × List UInt64))),
    okRoundsE (rvT (ckP .two) ds τ) = true → decide s (rvT (ckP .two) ds τ) cols = .ok s₁ →
    ∃ (x : TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀)) (F' : Fork) (g : Forest.Heard),
      ((kLookupCRN L).toKind.block r).R.red.out a
          ((mapsT ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
        some ((x, a.1.2), a.2) ∧
      fork s₁ = some F' ∧ heard s₁ = some g ∧ g.shape = r.c.h ∧
      ∀ (sO sP sJ : S) (clO clP clJ : List Cl) (GO GP GJ H : Fork),
        K3RanAt fork heard g F' objects sO clO GO → K3RanAt fork heard g F' planes sP clP GP →
        K3RanAt fork heard g F' join sJ clJ GJ →
        _root_.Fo.Later GO H → _root_.Fo.Later GP H → _root_.Fo.Later GJ H →
        ∀ (μ₀ : r.c.J₀ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
          (∀ c ∈ clO ++ clP ++ clJ,
            (form c).value Reading.gl
              (H.worldOf Reading.gl (fun j => zext μ₀ (placeOf mk pl (.mask j))) entry) = 0) →
          K3HostLaw r.c.h lm (endsOf r.c.h lm F.next (viewRounds ds τ)).zb0
            (endsOf r.c.h lm F.next (viewRounds ds τ)).zb1
            (fun k => (endsOf r.c.h lm F.next (viewRounds ds τ)).zk.getD k [])
            (fun p => zext μ₀ (placeOf mk pl p)) (forK Cb.Gl.E r.c.L a.1.1 (zext μ₀))
            (fun f => f.value Reading.gl
              (H.worldOf Reading.gl (fun j => zext μ₀ (placeOf mk pl (.mask j))) entry))
            (bit sP) (pin sP) (keys sJ) →
          (forA Cb.Gl.E r.c.h r.c.L).lk.out id id x (zext μ₀)

end VerifiableInference.OnPublicFiles
