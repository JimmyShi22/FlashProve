-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/RunA/ListedOwnDefs.lean: the compiled verifier's evaluable form that goes along the
positions read and the positions listed in every tree: the stored tables' (as in
OnBytes/RunA/ListedDefs.lean) and the chain's own. Of the rounds' wiring it takes only what it
reads. Definitions alone; the laws are in OnBytes/RunA/ListedOwnLaws.lean.

Why. (1) The library's forms walk `List.range (2 ^ depth)` for each own tree, twice. The strict
format (Run/ThinDefs.lean, `sCompP`) asks at every leaf at whose position an opening stands: has
the component a root, is the position read, has the salt its length? The checks (`compP`) are the
read positions' checks by rising leaf. (2) A round's wiring (Iop/BatchWire.lean, `WireRB`) holds
`pt : Round.IsPoint`, whose field `finPos : Fintype r.Pos` is data: the list of all positions,
built when the record is built (Run/PlanQS.lean, `wireS`).
As with the stored tables, the typed string's field `opens` is a function on all positions, and the
verdict depends on its value at each. So the caller says at which leaves openings can stand, and
the equation asks that there are none elsewhere. At the library's own typing (Run/ParseThin.lean,
`toBPrfP`) `opens` is a look-up in finite tables (`atTT`), so the equation for `VXLO` has no
hypothesis left.

What the file contains.
  `WireRLess`, `WireSLess`: a round's wiring: what the evaluable forms read of `WireRB` (not
    `finPos`, `place`, `gr0`, `grJ`), and two functions more: the leaves at which the members of a
    set of positions stand, rising.
  `chainL`, `trL`: Run/ThinDefs.lean's `chainP` and `trP`, word for word, at that wiring.
  `sCompL`, `sSL`: the strict format along listed leaves.
  `optL`, `forestsL`: Run/ThinReads.lean's `forestsR`, with the library's `compP` along the read
    leaves.
  `strictPLO`, `forestsOfLO`, `afterPLO`, `verifyPLO`: ListedDefs.lean's `strictPL`, `forestsOfL`,
    `afterPL`, `verifyPL` with these.
  `wireLessS`, `wire0Less`, `wiresLessSL`: that wiring at a description's rounds (Run/PlanQS.lean's
    `wireS`, `wire0S`, `wiresSL`).
  `opensOfX`, `ownListedX`, `VXLO`, `otabsX`: the verifier at a description with two stored tables.
    `opensOfX`'s arguments salt, a, xs and dec are idle: `TYX`'s fields `place` and `sym` read C
    and ds alone.

What `VXLO` is. It is the compiled verifier on a part of its domain: the typed strings
`{ π with opens := opensOfX .. otabs, ext := extOf .. tabs }`. That part holds all that `toBPrfX`
returns (`toBPrfX_both`). It does not hold every typed string. `VXLO` tests neither `D.ok` nor that
`D.base.cfg` has 32 bytes (ListedDefs.lean's head says why that matters): the caller must test
both.

The own leaves' salts are not like the stored leaves'. The typed verifier tests the length of an
own leaf's salt alone (Run/ParseBS.lean's head, "To be declared with every use"). That its first
256 bits are the run's value is the typing's doing: `otabsX` lays `leafSalt run s` with
`run := o.run`, which is also the chain's salt `π.salt` at what `toBPrfX` returns. At free otabs
(the case of `vxlo_eq`) nothing ties the rows' salts to `π.salt`. But an own leaf always has a hash
call: `leafX` falls to Run/CodingFn.lean's `leafCall`, whose start is the salt's first 256 bits,
whatever they are. So there is no constant answer: the symbol is always part of what is hashed. By
reading: whoever writes an own row's salt chooses the first 32 bytes (the start) of that leaf's
hashed string; the leaf is then not the format's leaf. So the untrusted converter (the program that
turns a proof file's bytes into Lean data) must end at plain data before `otabsX` too, on another
ground than at the stored tables: the start decides what is hashed, and nothing that decides what
is hashed may come unchecked from the converter.

What no check sees of (π, otabs, tabs), by reading the bodies. The following are seen by neither
`VXLO` nor `verifyOneProtocol` at the typed string, so they are neither refused nor checked.
  Of tabs: ListedDefs.lean's list, (b) to (g).
  Of π: its own fields `opens` and `ext`, and `rtreq`. All rounds are local, so the chain never
    joins: `chainL` reads `rtreq` in the `.join` branch alone, and the test of the request tree
    (`reqPartB`) is true when the chain has no slot value. That slot < 2^0 and that path = [] are
    tested.
  Of otabs: a table behind an earlier table under the same tree's number; a row behind an earlier
    row at the same place; a row at a place that is no position of the tree (2^depth or more); a
    table under a number that is no round's tree; at an unread place, a row whose column has not
    the tree's width (`symSL` refuses it, so there is no opening; at a read place that is a
    refusal, also when a right row stands behind it); the digests of a row's path that the pruned
    walk does not read.
By `vxlo_eq` a yes of `VXLO` is a yes of `verifyOneProtocol` at the typed string made of π, otabs and tabs.
Of what is listed above, `rtreq` and the unread digests of the paths are part of that string; the
rest is no part of it. These files say nothing on soundness.
The tables of (π, otabs, tabs) are unsorted and the first hit wins. `verifyPLO_eq` also serves a
value whose tables are sorted by leaf number, once its hypothesis `ListedOK` is shown of that
value's function into `OneProtocolProof`.

Cost. The equations are theorems. The cost is not: it is a matter of the compiled code, of which no
theorem here speaks, and nothing on time or memory is written down here. By reading the bodies it
goes with the rows listed and read: about (listed positions) times (rows + reads) for the strict
format's test, and rows times depth for the trees' walks. The caller decides how many rows are
listed. No list and no walk of length 2^a or 2^depth comes in. A position is nested one `Sum.inr`
deep for each round before it, so each comparison in a search of the set of reads costs up to the
number of rounds. The run of which `vxlo_compiled` (OnBytes/RunA/ListedCompiled.lean
[not in this library]) speaks also holds `toBPrfX`, `otabsX` and `tabsX`, and makes the tables
twice.
Still carried as data: `D.C` (`Run.PQ.CK`) and the skeleton's rounds (`RS`), whose fields hold
closures over `Fintype` instances of the rounds' verifier messages (the rounds' `finT`, which
`RS.up` alone calls; `CK`'s `fin`), and the closure `Lf`, whose body reaches `RS.up`. That these
closures are never called is not proved. A round's verifier message is b hash blocks, of the type
`Fin b → Dig 256` (Run/PlanPull.lean, `ckP`); where b is at least 1, one call would not end.

-/
import OnBytes.RunA.ListedDefs

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch

/-- What the evaluable forms read of a round's wiring, and the leaves of a set of positions in the
round's two trees. -/
structure WireRLess (lam K : ℕ) (r : RS) where
  decPos : DecidableEq r.Pos
  ofSyms : ((p : r.Pos) → r.Sym p) → r.Orc
  zero : (p : r.Pos) → r.Sym p
  depth0 : ℕ
  depthJ : ℕ
  has0 : Bool
  hasJ : Bool
  posAt0 : ℕ → Option r.Pos
  posAtJ : ℕ → Option r.Pos
  chal : (Fin K → Dig lam) → r.Chal
  pr0 : Bool
  prJ : Bool
  /-- the leaves of the shared component's tree at which members of the set stand, rising -/
  leaves0 : Finset r.Pos → List ℕ
  /-- the same for the slot's component's tree -/
  leavesJ : Finset r.Pos → List ℕ

def WireSLess (lam K : ℕ) : List RS → Type
  | [] => Unit
  | r :: S => WireRLess lam K r × WireSLess lam K S

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-! ### The strict format along listed leaves -/

def sCompL (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ) :
    Bool :=
  js.all fun j => !decide (j < 2 ^ depth) || match posAt j with
    | none => true
    | some p => match f p with
      | none => true
      | some op => hasRoot && isRead p && decide (op.salt.length = sMT)

/-- `ls`: round by round, the listed leaves of the two trees. -/
def sSL (sMT : ℕ) :
    (S : List RS) → WireSLess lam K S → RootsOfChain lam (up S) →
    (OPos (up S) → Bool) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) →
    List (List ℕ × List ℕ) → Bool
  | [], _, _, _, _, _ => true
  | r :: S, (w, W), (rt, rts), isRead, f, ls =>
      sCompL sMT r w.posAt0 w.depth0 rt.1.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) (ls.headD ([], [])).1 &&
      sCompL sMT r w.posAtJ w.depthJ rt.2.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) (ls.headD ([], [])).2 &&
      sSL sMT S W rts (fun p => isRead (.inr p)) (fun p => f (.inr p)) ls.tail

/-! ### The checks along the read leaves -/

def optL (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ) :
    Option (List (Check lam (Lf ()))) :=
  match rt with
  | none => some []
  | some c => compP Lf r posAt depth emb c isRead f js

def forestsL :
    (S : List RS) → WireSLess lam K S →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → Finset (OPos (up S)) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam (Lf ())))
  | [], _, _, _, _, _ => some []
  | r :: S, (w, W), emb, (rt, rts), R, f =>
      haveI : DecidableEq r.Pos := w.decPos
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      match optL Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)) (w.leaves0 R0),
        optL Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)) (w.leavesJ R0),
        forestsL S W (fun p => emb (.inr p)) rts
          (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (splitP Lf w.pr0
              ⟨w.depth0, fun _ => rt.1.join.getD default, a.map fun c => (0, c)⟩ ++
            (splitP Lf w.prJ ⟨w.depthJ, fun _ => rt.2.join.getD default, b.map fun c => (0, c)⟩ ++
              c))
      | _, _, _ => none

/-! ### The local transcript -/

def trL :
    (S : List RS) → (A : RoundSplits (up S)) → WireSLess lam K S → RootsOfChain lam (up S) → Plains (up S) →
    Rho (up S) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Tr (up S)
  | [], _, _, _, _, _, _ => ()
  | r :: S, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f =>
      ((w.ofSyms fun p => match rootP r a rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.zero p, effP r a rt pl), c, trL S A W rts pls ρ fun p => f (.inr p))

/-! ### The chain -/

variable (g : Fam (spec lam K (Lf ())))

def chainL (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → WireSLess lam K S →
    (PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) → ℕ → Phase lam → List (Dig lam) →
    Plains (up S) → Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam)
  | [], _, _, _, _, ph, _, _ => some ((), (), ph)
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (OracleName.fb t)
                  (⟨i, h.withLate (if late = some i then x else none), rt,
                    embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam (Lf ()) t)
              (chainL early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)
          | none => none
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (OracleName.fb t) (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam (Lf ()) t)
              (chainL early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2)
          | none => none
      | some (.join ρ) =>
          match takeRt w.hasJ rts with
          | some (rtj, rts1) =>
              match takeRt w.has0 rts1 with
              | some (rt0, rts') =>
                  let c : Dig lam :=
                    g (OracleName.g t) (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam (Lf ()) t)
                  let ans : (Fin K → Dig lam) × Dig lam :=
                    g (OracleName.fb t)
                      (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                        embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam (Lf ()) t)
                  (chainL early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                      (.shr (List.ofFn ans.2) c) rts' pls).map
                    fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)
              | none => none
          | none => none
      | none => none

/-! ### The verifier -/

variable {Y : Type} {E : ExtSpec} (ord : Finset E.Pos → List E.Pos)

def strictPLO (sMT sFS : ℕ) (P : PS Y E) (sh : WireSLess lam K P.S)
    (decO : DecidableEq (OPos (up P.S))) (we : WireELess E) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (listed : List E.Pos) (own : List (List ℕ × List ℕ)) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  haveI := decO
  haveI := we.dec
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ cntP P.S rts) &&
    sSL sMT P.S sh rts (fun p => decide (p ∈ R)) π.opens own &&
    strictListed sMT (fun p => decide (p ∈ Re)) π.ext listed &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty)

def forestsOfLO (P : PS Y E) (sh : WireSLess lam K P.S) (we : WireELess E)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam (Lf ()))) :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match forestsL Lf P.S sh embS rts R π.opens,
        forestRead Lf we embE cms π.ext (ord Re) with
  | some a, some b => some (a ++ b)
  | _, _ => none

def afterPLO (P : PS Y E) (sh : WireSLess lam K P.S) (we : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfLO Lf ord P sh we embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (we.build fun p => (π.ext p).map Opening.sym)
            (trL P.S P.ann sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- **The verifier, along the positions read and listed in every tree.** -/
def verifyPLO (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (sh : WireSLess lam K P.S) (decO : DecidableEq (OPos (up P.S))) (we : WireELess E)
    (nOpen maxDepth : ℕ) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) (listed : List E.Pos) (own : List (List ℕ × List ℕ)) : Bool :=
  match chainL Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictPLO sMT sFS P sh decO we depthReq x π listed own ρ rts ph then
      afterPLO Lf g ord P sh we nOpen maxDepth embS embE depthReq cms x π ρ rts ph
    else false

/-! ### At a description's rounds -/

/-- What `WireRLess` keeps of Run/PlanQS.lean's `wireS`. A position is the leaf of its number. -/
def wireLessS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    WireRLess 256 (K + 1) (roundS C d) where
  decPos := inferInstanceAs (DecidableEq (Fin (posN d.tree)))
  ofSyms := fun f => f
  zero := fun _ _ => 0
  depth0 := 0
  depthJ := depthOf d.tree
  has0 := false
  hasJ := d.tree.isSome
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < posN d.tree then some ⟨j, h⟩ else none
  chal := chalGrind (chal d.entry d.kind) d.entry.work
  pr0 := false
  prJ := true
  leaves0 := fun _ => []
  leavesJ := fun R => ((R.image fun p => p.val).sort (· ≤ ·)).filter fun j => decide (j < 2 ^ depthOf d.tree)

/-- What `WireRLess` keeps of Run/PlanQS.lean's `wire0S`. -/
def wire0Less (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    WireRLess 256 (K + 1) (s0 C) where
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  zero := fun p => p.elim
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := chalGrind (chal e0 .nothing) 0
  pr0 := false
  prJ := false
  leaves0 := fun _ => []
  leavesJ := fun _ => []

def wiresLessSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → WireSLess 256 (K + 1) (SL C ds)
  | [] => ()
  | d :: ds => (wireLessS C K chal d, wiresLessSL C K chal ds)

/-! ### At a description with two stored tables -/

/-- The own trees' openings as Run/ParseThin.lean's `toBPrfP` lays them: a look-up in the tables of
all trees. -/
def opensOfX (salt : ℕ) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool)
    (otabs : List (Nat × List (Nat × Row3))) (p : OPos (Twin.up (SOf C ds))) :
    Option (Opening 256 (OSym (Twin.up (SOf C ds)) p)) :=
  atTT ((TYX salt C ds a xs dec).sym p) otabs ((TYX salt C ds a xs dec).place p).1
    ((TYX salt C ds a xs dec).place p).2

/-- Round by round, the leaves that the tables list: none for the round in front; for a round with
a tree, the places listed in the first table under that tree's number (for a round without a tree
the list is idle: `posAtJ` gives no position). -/
def ownListedX (ds : List RD) (otabs : List (Nat × List (Nat × Row3))) : List (List ℕ × List ℕ) :=
  ([], []) :: ds.map fun d => ([], ((otabs.lookup (trNo d.tree)).getD []).map Prod.fst)

/-- **The verifier.** Of the typed string π all fields but `opens` and `ext` go into the string (no
check reads `rtreq`: see the head). The own trees' openings are the library's look-up `atTT` in the
tables `otabs`; the stored tables' openings are the library's look-up `extOf` in the tables
`tabs`. -/
def VXLO (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) : Bool :=
  verifyPLO (lam := 256) (K := D.K + 1)
    (fun _ => LkX (I := Unit) (RI := Unit) D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, []))
      (fun _ => some ()))
    (famXK D dec (D.K + 1)) (readsInOrder2 (2 ^ D.a)) id none
    (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wire0Less D.C D.K (chalP D.base.plan.field D.K),
      wiresLessSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (decOS D.C D.ds) (weLessX D.a) (nOpen D.ds + (D.xs.map (·.count)).sum) (max (maxDepth D.ds) D.a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
    { π with
      opens := opensOfX D.base.plan.salt D.C D.ds D.a D.xs dec otabs
      ext := extOf D.a D.base.cfg tabs }
    (listedX D.a tabs) (ownListedX D.ds otabs)

/-- The own trees' tables as `Run.PQ.toBPrfX` (through `toBPrfP`) makes them. -/
def otabsX (xs : List XO) (o : _root_.Fmt.ChainOut) : List (Nat × List (Nat × Row3)) :=
  match o.run with
  | none => []
  | some run => (opensB (offStored xs o)).map fun x => (x.1, x.2.2.table run x.2.2.paths)

end OnBytes.RunA
