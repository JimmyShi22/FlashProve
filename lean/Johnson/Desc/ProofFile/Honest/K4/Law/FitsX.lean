-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitsX.lean: NO HYPOTHESIS. The public test on the parts of the
feed-forward layers' own rounds (`k4Fits`, Honest/K4/Part.lean), CUT CLAUSE BY CLAUSE, each clause a
Bool of its own under a name, so that a compiled program can ask them one at a time, at public
parameters. Five definitions, and one equation with its proof.

What is here. `k4Fits` is four tests as one; the fourth, `k4MakersFit`, is fifteen clauses as one.
`fitsClause Q fo tokv i` is clause number i of the eighteen with a name for a print; it computes
that clause alone. `fitsClauses` lists all eighteen, and `fitsClauses_all` says that their "and" is
`k4Fits`: so nothing is typed apart from the test. `k4ZeroLook P`: a value for what the lookup in
front has sampled, with the layout's shape, the three fields that K4's parts read at the layout's
sizes with every element 0, `leaves` empty, and the other fields at their defaults.
`k4PubAtX X hp g r0`: the public data of the place in group g, of public parameters X and the
group's plan hp, as `k4PubOf` lays them. `fitsClauseX X r0 g i`: clause i at group g of X, at the
zero look and as many zero tokens as the layout counts; nothing where X has no plan for the group.
THE EIGHTEEN. 0 the table: the parts' moves and coins against the verifier's table of rounds · 1 the
sizes of what the lookup has sampled · 2 the tokens: as many as the layout counts, each below the
vocabulary's size; the first group alone · 3, 4 the two long lists of scalars (the sums of limb
products · the row products) have their stated lengths · 5 to 11 the seven masked sumchecks' jobs,
in the rounds' order (the squares · the row products · the second token sumcheck · the batched
sumcheck · the first and the second gated product · the merge): each is made and has its call's
public shape · 12 the merge joins as many claims as the plan counts · 13 to 16 four lists of powers
have their numbers · 17 each claim that the merge joins passes the verifier's own test on a claim's
sizes.

  `fitsClause Q fo tokv i`   clause number i of the eighteen, with a name for a print
  `fitsClauses`   all eighteen
  `fitsClauses_all`   **their "and" is `k4Fits`**
  `k4ZeroLook P`   a value for what the lookup in front has sampled: the layout's shape, the three
      fields that K4's parts read at the layout's sizes with every element 0, `leaves` empty, and
      the other fields at their defaults
  `k4PubAtX X hp g r0`   the public data of the place in group g, as `k4PubOf` lays them
  `fitsClauseX X r0 g i`   clause i at group g of X, at the zero look and zero tokens

Not shown here. THAT ANY CLAUSE IS TRUE ANYWHERE. Five of the eighteen (3 · 13 to 16) compare a list
with the number by which it is itself made, and are true at every public data: 13 to 16 by
`powers_fit` (Law/FitPowers.lean), 3 by `wSums_length` (Law/W/FitNorms.lean); neither is called
here. A printed true or false is a printed fact: it gives no term of Lean. ALL THAT IS READ IS
PUBLIC: the layout, the scales, the plan's numbers, the weights' layout; in the makers' input every
cell, weight and token is 0, and K4's own sampled elements are 0; what the lookup has sampled (fo)
and the request's tokens (tokv) are the caller's in `fitsClause` and `fitsClauses`; in `fitsClauseX`
they are `k4ZeroLook` and zero tokens; no weight and no witness is read. THE CLAUSES 3 TO 12 AND 17
EACH DO A MAKER's WHOLE WORK at the zero input (3 and 4 make their lists whole before they count
them); in 5 to 12 and 17, at a model's size, tables of 2 ^ mu entries are built; 7 and 8 make what
the two jobs share anew each time. Cost: not measured. r0, the number of rounds in front of the
place: by reading, no clause's answer hangs on it (so many empty challenges are laid in front and
dropped again): 0 is the cheapest value. Nothing on soundness, on completeness or on any other
property.

Kin. Sought: by statement, to the letter and up to the bound letters, and by short name, among the
theorems of the library and of files that are no part of it yet, as they lay with the writer: no
hit. Clause 0 as a theorem, under the library's hypothesis: `tableFits_head`
(Law/TableFitsMember.lean). Not sought: twins of the five definitions in other letters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (ledNS ledNP Forest.Heard Verify.Public)
open OnBytes.Model.Layer (nEndT HPlan2)
open OnBytes.Desc.First.K4.Honest

/-- **Clause number i of the eighteen, with its name.** The lines 3 to 17 are `k4MakersFit`'s own,
in its order. From 18 on: true, under a name that says so. -/
def fitsClause (Q : K4Pub) (fo : Forest.Heard) (tokv : Array Nat) (i : Nat) : String × Bool :=
  let y := Q.P.y
  let w := k4ZeroIn Q fo
  let s (k : Nat) : Pts := k4ZeroPts Q fo ((starts Q).getD k 0)
  let b (k : Nat) : Pts := k4ZeroPts Q fo ((rowsNamed Q .batSigma).getD k 0)
  let fits (k : Nat) (j : Option Job) : Bool :=
    j.any (k4JobFits ((k4Shapes Q).getD k ⟨0, [], none⟩))
  match i with
  | 0 => ("0 the table", k4TableFits Q)
  | 1 => ("1 the lookup's sizes", k4LookFits Q fo)
  | 2 => ("2 the tokens", k4TokensFit Q tokv)
  | 3 => ("3 the sums of limb products: their number",
      (wSums Q w (b 0)).length == ledNS y.h.xl * y.NI)
  | 4 => ("4 the row products: their number",
      (rowProducts Q w (b 1)).length == ledNP y.h.xl * y.NI)
  | 5 => ("5 the job of the squares", fits 0 (jobSquares Q w (s 0)))
  | 6 => ("6 the job of the row products", fits 1 (jobRows Q w (s 1)))
  | 7 => ("7 the job of the second token sumcheck", fits 2 (jobTerms Q w (s 2)))
  | 8 => ("8 the job of the batched sumcheck",
      fits 3 (jobStack Q w (s 3) (Array.replicate (nEndT y) zeroE)))
  | 9 => ("9 the job of the first gated product", fits 4 (jobGated Q w (s 4)))
  | 10 => ("10 the job of the second gated product", fits 5 (jobGated2 Q w (s 5)))
  | 11 => ("11 the job of the merge", fits 6 (jobMerge Q w (s 6)))
  | 12 => ("12 the merge's claims: their number",
      (mergeClaimsAt Q w (s 6)).any fun l => l.length == Q.hp.NCL)
  | 13 => ("13 the powers gp: their number", (s 0).gp.size == ledNS y.h.xl)
  | 14 => ("14 the powers omV: their number", (s 1).omV.size == ledNP y.h.xl * y.NI)
  | 15 => ("15 the powers om: their number", (s 3).om.size == 2)
  | 16 => ("16 the powers rhoW: their number", (s 6).rhoW.size == Q.hp.NCL)
  | 17 => ("17 the merge's claims: their sizes",
      (mergeClaimsAt Q w (s 6)).any fun l =>
        l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)
  | _ => ("there is no such clause", true)

/-- All eighteen. -/
def fitsClauses (Q : K4Pub) (fo : Forest.Heard) (tokv : Array Nat) : List (String × Bool) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17].map (fitsClause Q fo tokv)

/-- **The "and" of the eighteen is the test.** -/
theorem fitsClauses_all (Q : K4Pub) (fo : Forest.Heard) (tokv : Array Nat) :
    ((fitsClauses Q fo tokv).all fun x => x.2) = k4Fits Q fo tokv := by
  simp only [fitsClauses, fitsClause, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    k4Fits, k4MakersFit, Bool.and_true, Bool.and_assoc]

/-- **A value for what the lookup in front has sampled**: the layout's shape; each of the three
fields that K4's parts read (zx, e, zk) has the size with which the lookup's own text makes it, and
every element of these three is 0. `leaves` is empty; every other field stands at the structure's
default (`a`, the product over the padding keys, is 1 there). -/
def k4ZeroLook (P : OnBytes.Model.Layer.Pub) : Forest.Heard :=
  let h := P.y.fo
  { shape := h, leaves := {}, zx := Array.replicate h.dT zeroE, e := Array.replicate h.NC zeroE
    zk := (Array.range h.NC).map fun c =>
      Array.replicate (((h.calls[c]?).map (·.n)).getD 0) zeroE }

/-- The public data of K4's place in group g, of public parameters and the group's plan: the fields
as `k4PubOf` lays them, where the proof covers attention: link and segment 2 g, piece 3. r0: the
number of rounds in front. -/
def k4PubAtX (X : Verify.Public) (hp : HPlan2) (g r0 : Nat) : K4Pub :=
  { P := X.layers, hp := hp, g := g, link := 2 * g, piece := 3, r0 := r0, seg := 2 * g }

/-- **Clause i at group g of public parameters**, at the zero look and zero tokens. Nothing where
there is no plan for the group. -/
def fitsClauseX (X : Verify.Public) (r0 g i : Nat) : Option (String × Bool) :=
  (X.G[g]?).map fun hp =>
    fitsClause (k4PubAtX X hp g r0) (k4ZeroLook X.layers) (Array.replicate X.layers.y.T 0) i

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.fitsClause
#print axioms ProofFile.Honest.K4.fitsClauses
#print axioms ProofFile.Honest.K4.fitsClauses_all
#print axioms ProofFile.Honest.K4.k4ZeroLook
#print axioms ProofFile.Honest.K4.k4PubAtX
#print axioms ProofFile.Honest.K4.fitsClauseX
