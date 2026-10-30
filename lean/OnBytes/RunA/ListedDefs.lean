-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/RunA/ListedDefs.lean: the compiled verifier's evaluable form that goes along the positions
read and the positions listed, and never along all positions of a stored table. Definitions alone;
the laws are in OnBytes/RunA/ListedLaws.lean.

Why. The library's evaluable forms (Run/ThinDefs.lean to Run/ThinExtReads.lean: `verifyP`,
`verifyPB`, `verifyPR`, `verifyPX`) walk the wiring's list `all` of the external strings' positions
twice. At two stored tables of depth a that list has 2 * 2^a cells.
  Walk 1 (Compile/Bcs.lean, `strictExt`) asks at every position at which the typed string has an
    opening: is the position read, and has the salt its length? So one opening of the typed string
    at one position that is not read makes the verifier refuse. That is said of the typed string,
    not of a row of the tables `tabs`.
  Walk 2 (Run/ThinDefs.lean, `extWP`) makes the checks of the positions read, in the order of
    `all`, and gives none if one of them has no opening.
The typed string's field `ext` is a function on all positions, and the verdict depends on its value
at each. So (a remark, not a theorem) no form can be equal to the library's at every typed string
and look at fewer places. What can be had: the caller says, beside the string, at which positions
openings can stand (`listed`), and the equation then asks that `ext` is none elsewhere. At the
library's own typing of a file (`Run.PQ.toBPrfX`) `ext` is a look-up in finite lists
(`Run.PQ.extOf`), and the hypothesis is proved of `extOf` for all lists (`extOf_listed`,
ListedLaws.lean). So the equation for `VXL` has no hypothesis left.

What `VXL` is. It is the compiled verifier on a part of its domain: the typed strings
`{ π with ext := extOf D.a D.base.cfg tabs }`. That part holds all that `toBPrfX` returns
(`toBPrfX_ext`). It does not hold every typed string: every opening that `extOf` gives has the
symbol (the position's own place, a column) and a salt that begins with cfg's bits.

Why `extOf` stays on the verifier's side (by reading, not proved). `extOf` lays cfg's bits in front
of every stored leaf's salt. At the oracle functions `famX` a stored table's leaf has a hash call
only if the first 256 bits of its typed salt are `D.base.cfg` (Run/PlanQXRun.lean, `leafX`);
otherwise the answer is a constant, whatever the symbol, and the verifier tests the salt's length
alone. `VXL` takes cfg from the description D, never from the caller's π or tabs. So the untrusted
converter (the program that turns a proof file's bytes into Lean data) must end at plain data
before `extOf`; it may not hand over a typed `ext`. This takes `D.base.cfg` to have 32 bytes: at
another size `leafX`'s comparison fails for every stored leaf that `extOf` lays with a salt of the
length that the strict format asks, and all their answers are the constant. `VXL` tests neither
that nor `D.ok`: the caller must test both.

What no check sees of (π, tabs), by reading the bodies. The map from (π, tabs) to
`{ π with ext := extOf .. tabs }` is total, many to one and not onto. The following are seen by
neither `VXL` nor `verifyOneProtocol` at that string, so they are neither refused nor checked:
  (a) π's own field `ext`;
  (b) a table behind an earlier table under the same flag (`List.lookup` takes the first hit);
  (c) a row behind an earlier row at the same place;
  (d) a row at a place that is 2^a or more;
  (e) at an unread place, the places of `idx` beyond the shortest of `cols`, `salts` and `paths`
      (the zips cut them; at a read place that is a refusal, since no opening stands where one is
      read);
  (f) `OpenB`'s fields `a` and `given` (the paths are the triple's third part);
  (g) the digests of a row's path that the pruned walk does not read (`pr := true`: where two
      opened vertices are siblings, neither path's entry of that level is read; `wellP` tests a
      path's length alone; at `toBPrfX`'s strings `Octopus.fill` lays the default digest there);
  (h) π's field `rtreq`: all rounds are local, so the chain never joins and no check reads it;
  (i) in the paths of `π.opens`, the digests that the pruned walk does not read.
`toBPrfX`'s own tests (`OpenB.ok`, and the opening's depth against a) shut out (c), (d), (e) and a
wrong depth; they do not shut out (b). By `vxl_eq` a yes of `VXL` is a yes of `verifyOneProtocol` at the
typed string made of π and tabs. Items (a) to (f) are no part of that string; items (g) to (i) are
part of it. These files say nothing on soundness. Nothing on size carries over from the typed
string to tabs, and neither does a sentence such as "VXL refuses surplus rows in the tables".
The tables of (π, tabs) are unsorted and the first hit wins; (b) and (c) come from that.
`verifyPL_eq` also serves a value whose tables are sorted by leaf number, once its hypothesis h2
(an opening stands at listed positions alone) is shown of that value's function into `OneProtocolProof`.

What the file contains.
  `WireELess`: the wiring of the external strings less its list `all`.
  `strictListed`: walk 1 along the listed positions.
  `checksRead`, `forestRead`: walk 2 along a list of the positions read.
  `strictPL`, `forestsOfL`, `afterPL`, `verifyPL`: Run/ThinDefs.lean's `strictP` and
    Run/ThinReads.lean's `forestsOfR`, `afterPR`, `verifyPR` with these two walks, and with the
    wiring's pieces as separate arguments.
  `posOfNumber2`, `readsInOrder2`: the positions read of two strings of length n, in the order of
    `WireE.two`'s `all`.
  `listedX`: the positions that the tables' openings list.
  `weLessX`, `VXL`: the verifier at a description with two stored tables (`Run.PQ.XD`).
  `tabsX`: the tables as `Run.PQ.toBPrfX` hands them to `Run.PQ.extOf`.
`tabsX` and `listedX` repeat what OnBytes/Tie/StoredExt.lean holds: `tabsX xs o` is
`Tie.tabsOf (storedB xs o)`, and `listedX` at `Tie.tabsOf sto` is the list of which `Tie.readOf` is
the finite set. They are written again because importing StoredExt.lean would draw
Run.PageIsProofs, Run.Toy1TieChecks and OnBytes.Tie.StoredWalk into a native program's
initialisers. ListedLaws.lean joins them (`tabsX_tabsOf`, `listedX_tabsOf`). Mathlib is on the
path: `PS.extReads` is a Finset, and `readsInOrder2` uses `Finset.image` and `Finset.sort`.
There is no bitmap and no hash set: "is p read" is asked at the listed positions alone, by a search
in the set.

Cost. The equations are theorems. The cost is not: it is a matter of the compiled code, of which no
theorem here speaks, and nothing on time or memory is written down here. By reading the bodies it
goes with the rows listed and read: about (listed positions) times (rows + reads) for the strict
format's test, and rows times depth for the trees' walks. The caller decides how many rows are
listed. No list and no walk of length 2^a comes in.
Not removed here: three costs of 2^depth for each of the chain's own trees. They are `sSP`'s walk,
`forestsR`'s walk, and the list of all positions in Run/PlanQS.lean's `wireS`
(`pt.finPos : Fintype`, which is data), which `VXL` builds by calling `wiresSL`.
OnBytes/RunA/ListedOwnDefs.lean (`VXLO`) removes all three.

-/
import Run.PlanQXFastR

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch

/-! ### For any protocol with external strings -/

/-- The wiring of the external strings (Iop/Wire.lean, `WireE`) less its list of all positions. -/
structure WireELess (E : ExtSpec) where
  which : E.Pos → ℕ
  leaf : E.Pos → ℕ
  depth : ℕ
  build : (E.Pos → Option E.Sym) → E.Str
  dec : DecidableEq E.Pos
  pr : Bool

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-- The strict format's test of the external openings (Compile/Bcs.lean, `strictExt`), at the
listed positions. -/
def strictListed {E : ExtSpec} (sMT : ℕ) (isRead : E.Pos → Bool)
    (f : E.Pos → Option (Opening lam E.Sym)) (listed : List E.Pos) : Bool :=
  listed.all fun p => match f p with
    | none => true
    | some op => isRead p && decide (op.salt.length = sMT)

/-- The checks of the external openings (Run/ThinDefs.lean, `extWP`), along a list of positions,
all of them taken as read. -/
def checksRead {E : ExtSpec} (we : WireELess E) (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam))
    (f : E.Pos → Option (Opening lam E.Sym)) :
    List E.Pos → Option (List (ℕ × Check lam (Lf ())))
  | [] => some []
  | p :: ps =>
      match f p, checksRead we emb cms f ps with
      | some op, some cs =>
        some ((we.which p,
              ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
                cms.getD (we.which p) default, we.depth⟩) :: cs)
      | _, _ => none

/-- The forest of the external openings (Run/ThinDefs.lean, `forestExtP`), along a list of
positions. -/
def forestRead {E : ExtSpec} (we : WireELess E) (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam))
    (f : E.Pos → Option (Opening lam E.Sym)) (rd : List E.Pos) :
    Option (List (Forest lam (Lf ()))) :=
  (checksRead Lf we emb cms f rd).map fun cs =>
    splitP Lf we.pr ⟨we.depth, fun t => cms.getD t default, cs⟩

variable (g : Fam (spec lam K (Lf ()))) {Y : Type} {E : ExtSpec} (ord : Finset E.Pos → List E.Pos)

/-- Run/ThinDefs.lean's `strictP`, the external openings tested at the listed positions. -/
def strictPL (sMT sFS : ℕ) (P : PS Y E) (sh : RoundsQueryLayout lam K (up P.S) P.ann)
    (decO : DecidableEq (OPos (up P.S))) (we : WireELess E) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (listed : List E.Pos) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S))
    (ph : Phase lam) : Bool :=
  haveI := decO
  haveI := we.dec
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ cntP P.S rts) &&
    sSP sMT P.S P.ann sh rts (fun p => decide (p ∈ R)) π.opens &&
    strictListed sMT (fun p => decide (p ∈ Re)) π.ext listed &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty)

/-- Run/ThinReads.lean's `forestsOfR`, the external checks along the list that `ord` makes of the
set of reads. -/
def forestsOfL (P : PS Y E) (sh : RoundsQueryLayout lam K (up P.S) P.ann) (we : WireELess E)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam (Lf ()))) :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match forestsR Lf P.S P.ann sh embS rts R π.opens,
        forestRead Lf we embE cms π.ext (ord Re) with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- Run/ThinReads.lean's `afterPR` at `forestsOfL`. -/
def afterPL (P : PS Y E) (sh : RoundsQueryLayout lam K (up P.S) P.ann) (we : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfL Lf ord P sh we embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (we.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- **The verifier, along the external positions read and listed.** The wiring comes in pieces: sh,
decO, we, nOpen, maxDepth. -/
def verifyPL (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (sh : RoundsQueryLayout lam K (up P.S) P.ann) (decO : DecidableEq (OPos (up P.S))) (we : WireELess E)
    (nOpen maxDepth : ℕ) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) (listed : List E.Pos) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictPL sMT sFS P sh decO we depthReq x π listed ρ rts ph then
      afterPL Lf g ord P sh we nOpen maxDepth embS embE depthReq cms x π ρ rts ph
    else false

/-! ### Two strings of length n -/

/-- The position of two strings of length n that has the number i (Run/ThinExtReads.lean,
`idx2`). -/
def posOfNumber2 (n i : ℕ) : Option (Fin n ⊕ Fin n) :=
  if h : i < n then some (.inl ⟨i, h⟩)
  else if h' : i - n < n then some (.inr ⟨i - n, h'⟩) else none

/-- The members of a set of positions of two strings, by rising number: the first string's, then
the second's. -/
def readsInOrder2 (n : ℕ) (R : Finset (Fin n ⊕ Fin n)) : List (Fin n ⊕ Fin n) :=
  ((R.image (idx2 n)).sort (· ≤ ·)).filterMap (posOfNumber2 n)

/-! ### At a description with two stored tables -/

/-- The positions that the tables' openings list. -/
def listedX (a : ℕ) (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    List (Fin (2 ^ a) ⊕ Fin (2 ^ a)) :=
  (tabs.flatMap fun T => T.2.1.idx.map fun x => (T.1, x)).filterMap (xPos (2 ^ a))

/-- Run/PlanQX.lean's `weX` less its list of all positions, written out. -/
def weLessX (a : ℕ) : WireELess (twoExternalStrings (2 ^ a) SgX) where
  which := fun p => p.elim (fun _ => 0) (fun _ => 1)
  leaf := fun p => p.elim (fun q => q.val) (fun q => q.val)
  depth := a
  build := fun f => (fun p => (f (.inl p)).getD (0, []), fun p => (f (.inr p)).getD (0, []))
  dec := inferInstanceAs (DecidableEq (Fin (2 ^ a) ⊕ Fin (2 ^ a)))
  pr := true

/-- **The verifier.** Of the typed string π all fields but `ext` go into the string (no check reads
`rtreq`: see the head); the external openings are the library's look-up `Run.PQ.extOf` in the
tables `tabs`. -/
def VXL (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) : Bool :=
  verifyPL (lam := 256) (K := D.K + 1)
    (fun _ => LkX (I := Unit) (RI := Unit) D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, []))
      (fun _ => some ()))
    (famXK D dec (D.K + 1)) (readsInOrder2 (2 ^ D.a)) id none
    (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wire0S D.C D.K (chalP D.base.plan.field D.K), wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (decOS D.C D.ds) (weLessX D.a) (nOpen D.ds + (D.xs.map (·.count)).sum) (max (maxDepth D.ds) D.a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
    { π with ext := extOf D.a D.base.cfg tabs } (listedX D.a tabs)

/-- The tables as `Run.PQ.toBPrfX` hands them to `Run.PQ.extOf`. -/
def tabsX (xs : List XO) (o : _root_.Fmt.ChainOut) : List (Bool × OpenB × List (List (Dig 256))) :=
  (storedB xs o).map fun x => (x.1, x.2.2, x.2.2.paths)

end OnBytes.RunA
