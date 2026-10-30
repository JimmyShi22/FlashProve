-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/ToyWork.lean: a test: a small batch protocol with tests (proof of work) in a local
round, in the joining round and in a later shared round, a tree whose opened leaves are checked by a
pruned set of paths, two trees in a shared component, and an external string under a tree. The
compiled prover (OnBytes/Prover/Defs.lean) is run under 16 families of oracle functions that are not
constant and read every field of every query, and the compiled verifier (verifyOneProtocol) says yes
to each string.

Why. It tries the arms of the prover's text that the small file of OnBytes/Prover/ToyFileRun.lean
does not reach, before anything is proved of that text; and it shows that the three outcomes of the
prover all occur.

The rounds: r1, local: four bits under one tree of depth 2, a nonce; rJ, shared, the joining round:
a nonce; r2, shared: two bits and one more bit under two trees, a nonce; r3, local: nothing. Each
draws a block of four bits. Bit 0 of the blocks of r1, rJ, r2 is a test bit. The verifier reads two
neighbouring places of r1's string, one place of r2's string and its one more bit, and one place of
the external string; it accepts if the instance is true, the three test bits are 0, and all that it
reads is true.

Main names:
  `Q`, `wq`, `embS`   the protocol, its wire record, how a symbol is written into a leaf (a number)
  `gN n`             oracle functions: each answer's bits are bits of a number made of n and a code
                    of the query
  `run b cap n`      the prover's outcome under gN n (`runC`: at caps by round; `cap_by_round`); the
                    outer tree and its root are made under gN n too
  `all_yes`          at cap 40: a string, the interactive verifier's yes at the transcript,
                    verifyOneProtocol's yes
  `some_ranOut`, `some_nonce`, `no_format`   at cap 0 a search runs out under some gN n; at cap 40
                     some nonce is not 0; at an annotation that starts with a shared round the
                     outcome is noFormat
  `refusals`, `bent_*`   one field of the string turned: under how many of the 16 it is refused, as
                     counted: the test can fail; unturned: under none
  `ownSalt`, `ownPath`, `extSalt`, `extPath`   an opening's salt or path turned, the symbols kept:
                     so that a walk, pruned or outer, is seen to say no
  `explains`, `why_*`, `which_*`   WHY a turned string is accepted where it is: the verifier's value
                     is that of a named equation between digests, under each of the 16; and which
                     oracle collides
  `false_no`         at a strategy whose string holds a false bit everywhere verifyOneProtocol says no
                    throughout

Limits: a test, by evaluation in Lean's kernel, at 16 families of functions. Digests have four bits.
No law of the wire record is proved here. The list of roots reversed is refused under 15 of the 16;
under gN 8 the list reads the same backwards (`bent_rootsRev`, `rootsRev_same`). NOT UNDERSTOOD: the
kernel's check of the verifier's value at that one turned string under gN 8 fails for "= true" and
for "= false" alike, each time with an error that Lean could not print; at the unturned string, and
at the list reversed twice, it confirms the yes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import Compile.MerkleList
import Iop.WireOf
import Run.PlanQS
import Rom.Cache

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyWork
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The rounds -/

abbrev Blk : Type := Fin 1 → Dig 4

@[reducible] def r1 : Round where
  Orc := Fin 4 → Bool
  Pos := Fin 4
  Sym := fun _ => Bool
  rd := fun o p => o p
  Plain := ℕ
  Chal := Blk
  dOrc := fun _ => false
  dPlain := 0

@[reducible] def rJ : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => nomatch p
  Plain := ℕ
  Chal := Blk
  dOrc := ()
  dPlain := 0

@[reducible] def r2 : Round where
  Orc := (Fin 2 → Bool) × Bool
  Pos := Fin 2 ⊕ Unit
  Sym := fun _ => Bool
  rd := fun o p => match p with
    | .inl j => o.1 j
    | .inr _ => o.2
  Plain := ℕ
  Chal := Blk
  dOrc := (fun _ => false, false)
  dPlain := 0

@[reducible] def r3 : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => nomatch p
  Plain := Unit
  Chal := Blk
  dOrc := ()
  dPlain := ()

@[reducible] def sh : Shape := [r1, rJ, r2, r3]

@[reducible] def ann : RoundSplits sh :=
  (RAnn.allLocal r1, RAnn.ofShared .sh rJ, RAnn.ofShared .sh r2, RAnn.allLocal r3, PUnit.unit)

instance decO : DecidableEq (OPos sh) :=
  inferInstanceAs (DecidableEq (Fin 4 ⊕ (Empty ⊕ ((Fin 2 ⊕ Unit) ⊕ (Empty ⊕ Empty)))))

/-! ## The verifier -/

def tb (c : Blk) : Bool := c 0 0
def at4 (c : Blk) : Fin 4 := if c 0 1 then (if c 0 2 then 3 else 1) else (if c 0 2 then 2 else 0)
def at2 (c : Blk) : Fin 2 := if c 0 3 then 1 else 0

abbrev TrT : Type := r1.Msg × Blk × rJ.Msg × Blk × r2.Msg × Blk × r3.Msg × Blk × Unit
abbrev RhoT : Type := Blk × Blk × Blk × Blk × Unit

def acc (x : Bool) (y : Fin 2 → Bool) (τ : TrT) : Bool :=
  x && !tb τ.2.1 && !tb τ.2.2.2.1 && !tb τ.2.2.2.2.2.1 &&
    τ.1.1 (at4 τ.2.1) && τ.1.1 (at4 τ.2.1 + 1) &&
    τ.2.2.2.2.1.1.1 (at2 τ.2.2.2.2.2.1) && τ.2.2.2.2.1.1.2 && y (at2 τ.2.2.2.2.2.2.2.1)

def rds (ρ : RhoT) : Finset (OPos sh) :=
  {.inl (at4 ρ.1), .inl (at4 ρ.1 + 1), .inr (.inr (.inl (.inl (at2 ρ.2.2.1)))),
    .inr (.inr (.inl (.inr ())))}

@[reducible] def P : InteractiveOracleProof Bool (oneExternalString 2 Bool) where
  shape := sh
  blinded := fun _ => true
  extReads := fun _ ρ => {at2 (show RhoT from ρ).2.2.2.1}
  reads := fun _ ρ _ => rds ρ
  accept := fun x y τ => acc x y τ

@[reducible] def Q : BatchInteractiveOracleProof Bool (oneExternalString 2 Bool) := ⟨P, ann⟩

@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString 2 Bool) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

@[reducible] def pK : InteractiveOracleProof Unit (twoExternalStrings 2 Bool) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- The interface record; the body of a leaf is a number. -/
@[reducible] def L : BatchProtocolWithLeafBody Unit Bool where
  wordLength := 2
  Symbol := Bool
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => false
  decodeIndex := fun _ => some ()
  offline := pT
  link := pK
  maxBatchSize := 2
  onlineBatch := Q
  honestOfflineProver := _root_.Run.dummyH pT fun _ _ => false
  honestLinkProver := _root_.Run.dummyH pK fun _ => (fun _ => false, fun _ => false)
  honestOnlineBatchProver := _root_.Run.dummyB Q fun _ _ => false
  early := id
  late := none
  Bd := ℕ
  annT := PUnit.unit
  annL := PUnit.unit

/-! ## The wire records -/

/-- the test: bit 0 of the block; a nonce is its number -/
def gr : GrW Blk ℕ where
  b := 1
  tst := fun c _ => c 0 0
  set := fun z c i j => if j = 0 then z 0 else c i j
  more := 0
  put := fun n _ => n
  get := id

def ptJ : rJ.IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => nomatch p
  ofSyms_rd := fun _ => rfl
  zero := fun p => nomatch p

def pt3 : r3.IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => nomatch p
  ofSyms_rd := fun _ => rfl
  zero := fun p => nomatch p

def w1 : WireRB 4 1 r1 (RAnn.allLocal r1) where
  pt := ⟨inferInstanceAs (Fintype (Fin 4)), inferInstanceAs (DecidableEq (Fin 4)), fun f => f,
    fun _ _ => rfl, fun _ => rfl, fun _ => false⟩
  depth0 := []
  depthJ := [2]
  tree := fun _ => 0
  place := fun p => p.val
  posAt0 := fun _ _ => none
  posAtJ := fun k j => if k = 0 then (if h : j < 4 then some ⟨j, h⟩ else none) else none
  chal := id
  prJ := true
  grJ := some gr

def wJ : WireRB 4 1 rJ (RAnn.ofShared .sh rJ) where
  pt := ptJ
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := id
  gr0 := some gr

def w2 : WireRB 4 1 r2 (RAnn.ofShared .sh r2) where
  pt := ⟨inferInstanceAs (Fintype (Fin 2 ⊕ Unit)), inferInstanceAs (DecidableEq (Fin 2 ⊕ Unit)),
    fun f => (fun j => f (.inl j), f (.inr ())),
    fun _ p => match p with
      | .inl _ => rfl
      | .inr _ => rfl,
    fun _ => rfl, fun _ => false⟩
  depth0 := [1, 0]
  depthJ := []
  tree := fun p => match p with
    | .inl _ => 0
    | .inr _ => 1
  place := fun p => match p with
    | .inl i => i.val
    | .inr _ => 0
  posAt0 := fun k j =>
    if k = 0 then (if h : j < 2 then some (.inl ⟨j, h⟩) else none)
    else if k = 1 then (if j = 0 then some (.inr ()) else none) else none
  posAtJ := fun _ _ => none
  chal := id
  pr0 := true
  gr0 := some gr

def w3 : WireRB 4 1 r3 (RAnn.allLocal r3) where
  pt := pt3
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := id

def we : WireE (oneExternalString 2 Bool) := { WireE.one 2 Bool false with pr := true, depth := 1 }

def wq : ProtocolQueryLayout 4 1 Q := ⟨(w1, wJ, w2, w3, ()), we, decO, 5, 2⟩

def embS : (p : OPos sh) → OSym sh p → Body L
  | .inl j, b => 10 + 2 * j.val + (show Bool from b).toNat
  | .inr (.inr (.inl (.inl j))), b => 30 + 2 * j.val + (show Bool from b).toNat
  | .inr (.inr (.inl (.inr _))), b => 40 + (show Bool from b).toNat

def embE (b : Bool) : Body L := 100 + b.toNat

/-! ## Oracle functions that read every field of a query -/

def bitsN (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + 1 + b.toNat) 0
def digsN (l : List (Dig 4)) : ℕ := l.foldl (fun a d => 32 * a + 1 + bitsN (List.ofFn d)) 0
def optN : Option Bool → ℕ
  | none => 0
  | some b => 1 + b.toNat

def headN : Head 4 Bool → ℕ
  | .f1 cms x salt => 5 * (digsN cms + 7 * optN x + 31 * bitsN salt)
  | .f2 xl ρ => 5 * (optN xl + 3 * bitsN ρ) + 1
  | .f3 ρ0 c => 5 * (bitsN ρ0 + 1009 * bitsN c) + 2
  | .f4 cms r => 5 * (digsN cms + 2003 * bitsN r) + 3
  | .f5 ρ0 => 5 * bitsN ρ0 + 4

/-- a plain part: its round, its component, and the nonce that it holds -/
def plainN : PlainPart sh ann → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr n) => 1 + 8 * (show ℕ from n)
  | .inr (.inl (.inl n)) => 2 + 8 * (show ℕ from n)
  | .inr (.inl (.inr _)) => 3
  | .inr (.inr (.inl (.inl n))) => 4 + 8 * (show ℕ from n)
  | .inr (.inr (.inl (.inr _))) => 5
  | .inr (.inr (.inr (.inl (.inl _)))) => 6
  | .inr (.inr (.inr (.inl (.inr _)))) => 7

def mix (n c : ℕ) : Bool :=
  let h1 := ((c + 1) * 2654435761 + (n + 1) * 40503) % 4294967296
  let h2 := ((h1 ^^^ (h1 >>> 15)) * 2246822519) % 4294967296
  (h2 ^^^ (h2 >>> 13)) % 2 == 1
def dg (n c : ℕ) : Dig 4 := fun i => mix (n + 37 * i.val) c

def plainT : (t : Tag) → PlainPart (shapeOf L t) (annOf L t) → ℕ
  | .onl, z => plainN z
  | .test, z => nomatch z
  | .link, z => nomatch z

def fbN {t : Tag} (q : FbIn 4 L t) : ℕ :=
  q.round + 6 * headN q.head + 4001 * digsN q.rt + 97 * plainT t q.plain

def gN (n : ℕ) : Fam (typedOracleFamily 4 1 L)
  | .leaf => fun q => dg n (3 + 11 * (show ℕ from q.body) + 5003 * bitsN q.salt)
  | .node => fun q => dg n (1 + 13 * bitsN q.1 + 6007 * bitsN q.2)
  | .rleaf => fun q => dg n (2 + 17 * bitsN q)
  | .rnode => fun q => dg n (4 + 19 * bitsN q.1 + 7001 * bitsN q.2)
  | .fb _ => fun q => (fun _ => dg n (fbN q), dg n (fbN q + 1))
  | .fbw _ _ => fun q => (fun _ => dg n (fbN q), dg n (fbN q + 1))
  | .g t => fun q => dg n (q.round + 3 * bitsN q.ρ + 8009 * digsN q.rt + 101 * plainT t q.plain)
  | .ann => fun _ => ()
  | .other => fun _ => dg n 0

/-! ## The run -/

/-- all bits b -/
def σ (b : Bool) : Strat sh Unit :=
  ((fun _ => b, 0), fun _ => (((), 0), fun _ => (((fun _ => b, b), 0), fun _ => (((), ()),
    fun _ => ()))))

def co : Coins 4 L where
  salt := [true, false, true]
  leaf := fun i b k j => [(i + k + b.toNat) % 2 == 1, j % 2 == 1]
  pad := 0
  slot := 1
  path := [fun i => i.val % 2 == 0]
  rsalt := [false, true]

def y : Fin 2 → Bool := fun _ => true

/-- the tree over the external string, made under gN n -/
def xt (n : ℕ) : ℕ → TreeK 4 L := fun _ =>
  (treeO (K := 1) 1 fun j =>
    ⟨if h : j < 2 then embE (y ⟨j, h⟩) else 0, [j % 2 == 0, true]⟩).det (gN n)

def cms (n : ℕ) : List (Dig 4) := [(xt n 0).root]

def runAt (A : RoundSplits sh) (W : RoundsQueryLayout 4 1 sh A) (b : Bool) (cap n : ℕ) :
    Res (OneProtocolProof 4 (⟨P, A⟩ : BatchInteractiveOracleProof Bool (oneExternalString 2 Bool)) × Tr sh) :=
  (proveX (L := L) Tag.onl (⟨P, A⟩ : BatchInteractiveOracleProof Bool (oneExternalString 2 Bool)) ⟨W, we, decO, 5, 2⟩ embS
    (fun _ => .inl (.inl ())) some (cms n) true y (xt n) (σ b) co fun _ => cap).det (gN n)

/-- the outcome at caps by round -/
def runC (b : Bool) (cap : ℕ → ℕ) (n : ℕ) : Res (OneProtocolProof 4 Q × Tr sh) :=
  (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cms n) true y (xt n) (σ b)
    co cap).det (gN n)

/-- at one cap for all rounds -/
def run (b : Bool) (cap n : ℕ) : Res (OneProtocolProof 4 Q × Tr sh) := runC b (fun _ => cap) n

def yes (n : ℕ) (π : OneProtocolProof 4 Q) : Bool :=
  (verifyOneProtocol (L := L) 2 3 Tag.onl Q wq embS (fun z => z) some embE 1 (cms n) true π).det (gN n)

theorem all_yes : ((List.range 16).all fun n => match run true 40 n with
    | .ok z => yes n z.1 && acc true y z.2
    | _ => false) = true := by decide +kernel

theorem some_ranOut : ((List.range 16).any fun n => match run true 0 n with
    | .ranOut _ => true
    | _ => false) = true := by decide +kernel

/-- the caps are by round: at cap 40 in round 0 and cap 0 in the others no search of round 0 runs
out, and some search of a later round does -/
theorem cap_by_round : (((List.range 16).all fun n =>
    match runC true (fun i => if i = 0 then 40 else 0) n with
    | .ranOut 0 => false
    | _ => true) && (List.range 16).any fun n =>
    match runC true (fun i => if i = 0 then 40 else 0) n with
    | .ranOut _ => true
    | _ => false) = true := by decide +kernel

theorem some_ok_at_zero : ((List.range 64).any fun n => match run true 0 n with
    | .ok z => yes n z.1
    | _ => false) = true := by decide +kernel

theorem some_nonce : ((List.range 16).any fun n => match run true 40 n with
    | .ok z => decide ((show TrT from z.2).1.2 ≠ 0) && decide ((show TrT from z.2).2.2.1.2 ≠ 0) &&
        decide ((show TrT from z.2).2.2.2.2.1.2 ≠ 0)
    | _ => false) = true := by decide +kernel

def w1s : WireRB 4 1 r1 (RAnn.ofShared .sh r1) where
  pt := w1.pt
  depth0 := [2]
  depthJ := []
  tree := fun _ => 0
  place := fun p => p.val
  posAt0 := w1.posAtJ
  posAtJ := fun _ _ => none
  chal := id

/-- an annotation that starts with a shared round has no format -/
theorem no_format : (match runAt (RAnn.ofShared .sh r1, RAnn.ofShared .sh rJ, RAnn.ofShared .sh r2,
      RAnn.allLocal r3, PUnit.unit)
      (w1s, wJ, w2, w3, ()) true 40 0 with
    | .noFormat => true
    | _ => false) = true := by decide +kernel

theorem false_no : ((List.range 16).all fun n => match run false 40 n with
    | .ok z => !yes n z.1 && !acc true y z.2
    | _ => false) = true := by decide +kernel

/-- under how many of the 16 families the string, turned by f, is refused. (Digests have four bits:
a turned string passes where two digests collide.) -/
def refusals (f : OneProtocolProof 4 Q → OneProtocolProof 4 Q) : ℕ :=
  (List.range 16).countP fun n => match run true 40 n with
    | .ok z => !yes n (f z.1)
    | _ => false

theorem bent_none : refusals (fun π => π) = 0 := by decide +kernel
theorem bent_rootLess : refusals (fun π => { π with roots := π.roots.drop 1 }) = 16 := by
  decide +kernel
theorem bent_rootMore : refusals (fun π => { π with roots := π.roots ++ π.roots.take 1 }) = 16 := by
  decide +kernel
theorem bent_rootSwap : refusals (fun π => { π with roots := match π.roots with
    | a :: b :: l => b :: a :: l
    | l => l }) = 16 := by decide +kernel
theorem bent_rootFlip :
    refusals (fun π => { π with roots := π.roots.map fun d i => !d i }) = 16 := by
  decide +kernel
/-- the list of roots reversed: refused under each of the 15 families other than gN 8 -/
theorem bent_rootsRev : (((List.range 16).filter fun n => n != 8).all fun n =>
    match run true 40 n with
    | .ok z => !yes n { z.1 with roots := z.1.roots.reverse }
    | _ => false) = true := by decide +kernel
/-- under gN 8 the list of roots reads the same backwards, bit by bit: there the turned string is
the string itself -/
theorem rootsRev_same : (match run true 40 8 with
    | .ok z => (z.1.roots.map fun d => List.ofFn d).reverse == z.1.roots.map fun d => List.ofFn d
    | _ => false) = true := by decide +kernel
theorem bent_salt : refusals (fun π => { π with salt := [false, false, true] }) = 16 := by
  decide +kernel
theorem bent_rtreq : refusals (fun π => { π with rtreq := fun i => !π.rtreq i }) = 16 := by
  decide +kernel
theorem bent_path : refusals (fun π => { π with path := π.path.map fun d i => !d i }) = 15 := by
  decide +kernel
theorem bent_rsalt : refusals (fun π => { π with rsalt := [] }) = 12 := by decide +kernel
theorem bent_slot : refusals (fun π => { π with slot := 0 }) = 12 := by decide +kernel
theorem bent_opens : refusals (fun π => { π with opens := fun _ => none }) = 16 := by
  decide +kernel
theorem bent_ext : refusals (fun π => { π with ext := fun _ => none }) = 16 := by decide +kernel
theorem bent_extSym : refusals (fun π => { π with
    ext := fun p => (π.ext p).map fun o => { o with sym := !o.sym } }) = 16 := by decide +kernel
theorem bent_nonce : refusals (fun π => { π with
    plains := ((show ℕ × ℕ × ℕ × Unit × Unit from π.plains).1 + 1,
      (show ℕ × ℕ × ℕ × Unit × Unit from π.plains).2) }) = 16 := by decide +kernel

/-! ## Openings turned, the symbols kept -/

def flip1 : List Bool → List Bool
  | [] => []
  | b :: l => (!b) :: l
def flipD (d : Dig 4) : Dig 4 := fun i => !d i
def eqD (a b : Dig 4) : Bool := List.ofFn a == List.ofFn b
def nodeN (n : ℕ) (a b : Dig 4) : Dig 4 := gN n OracleName.node (List.ofFn a, List.ofFn b)
def rnodeN (n : ℕ) (a b : Dig 4) : Dig 4 := gN n OracleName.rnode (List.ofFn a, List.ofFn b)

/-- in every own opening the first bit of the salt flipped -/
def ownSalt (π : OneProtocolProof 4 Q) : OneProtocolProof 4 Q :=
  { π with opens := fun p => (π.opens p).map fun o => { o with salt := flip1 o.salt } }
/-- in every own opening every digest of the path flipped -/
def ownPath (π : OneProtocolProof 4 Q) : OneProtocolProof 4 Q :=
  { π with opens := fun p => (π.opens p).map fun o => { o with path := o.path.map flipD } }
/-- the like in the outer opening -/
def extSalt (π : OneProtocolProof 4 Q) : OneProtocolProof 4 Q :=
  { π with ext := fun p => (π.ext p).map fun o => { o with salt := flip1 o.salt } }
def extPath (π : OneProtocolProof 4 Q) : OneProtocolProof 4 Q :=
  { π with ext := fun p => (π.ext p).map fun o => { o with path := o.path.map flipD } }

theorem bent_ownSalt : refusals ownSalt = 16 := by decide +kernel
theorem bent_ownPath : refusals ownPath = 16 := by decide +kernel
theorem bent_extSalt : refusals extSalt = 14 := by decide +kernel
theorem bent_extPath : refusals extPath = 16 := by decide +kernel

/-! ## Why a turned string is accepted where it is -/

/-- the verifier's value at the string turned by f is crit's, under each of the 16 -/
def explains (f : OneProtocolProof 4 Q → OneProtocolProof 4 Q) (crit : ℕ → OneProtocolProof 4 Q → Bool) : Bool :=
  (List.range 16).all fun n => match run true 40 n with
    | .ok z => yes n (f z.1) == crit n (f z.1)
    | _ => false

/-- the climb from each outer opening of the string ends in the outer root -/
def extCrit (n : ℕ) (π : OneProtocolProof 4 Q) : Bool :=
  (List.finRange 2).all fun p => match π.ext p with
    | some o => eqD (climbF (nodeN n) o.path p.val (gN n OracleName.leaf ⟨embE o.sym, o.salt⟩))
        ((cms n).getD 0 default)
    | none => true

/-- the slot value that the verifier's chain finds -/
def slotOf (n : ℕ) (π : OneProtocolProof 4 Q) : Option (Dig 4) :=
  match (recomputeChainOfProof (L := L) Tag.onl Q wq (fun z => z) some (cms n) true π).det (gN n) with
  | some z => z.2.2.slotVal
  | none => none

/-- the climb in the request tree from the string's own data ends in the string's request root -/
def reqCrit (n : ℕ) (π : OneProtocolProof 4 Q) : Bool :=
  match slotOf n π with
  | some c => eqD (climbF (rnodeN n) π.path π.slot (gN n OracleName.rleaf (List.ofFn c ++ π.rsalt))) π.rtreq
  | none => false

theorem why_extSalt : explains extSalt extCrit = true := by decide +kernel
theorem why_extPath : explains extPath extCrit = true := by decide +kernel
theorem why_path : explains (fun π => { π with path := π.path.map flipD }) reqCrit = true := by
  decide +kernel
theorem why_rsalt : explains (fun π => { π with rsalt := [] }) reqCrit = true := by decide +kernel
theorem why_slot : explains (fun π => { π with slot := 0 }) reqCrit = true := by decide +kernel

/-- Which oracle collides at an accept. 0: refused; 1: the two leaves' digests are one (a collision
of the leaves' oracle); 2: they differ, so the nodes' oracle collides above them; 9: neither run nor
slot value. -/
def whichRsalt (n : ℕ) : ℕ :=
  match run true 40 n with
  | .ok z =>
    if yes n { z.1 with rsalt := [] } then
      match slotOf n z.1 with
      | some c =>
        if eqD (gN n OracleName.rleaf (List.ofFn c ++ [])) (gN n OracleName.rleaf (List.ofFn c ++ z.1.rsalt)) then 1
        else 2
      | none => 9
    else 0
  | _ => 9

def whichExtSalt (n : ℕ) : ℕ :=
  match run true 40 n with
  | .ok z =>
    if yes n (extSalt z.1) then
      if (List.finRange 2).all fun p => match z.1.ext p with
        | some o => eqD (gN n OracleName.leaf ⟨embE o.sym, flip1 o.salt⟩) (gN n OracleName.leaf ⟨embE o.sym,
                            o.salt⟩)
        | none => true then 1 else 2
    else 0
  | _ => 9

/-- at an accept of the string with slot := 0. 1: the leaf's digest and the path's digest are one,
so that both climbs hash one pair; 2: they differ: the request tree's nodes' oracle collides at (d,
p) | (p, d) -/
def whichSlot (n : ℕ) : ℕ :=
  match run true 40 n with
  | .ok z =>
    if yes n { z.1 with slot := 0 } then
      match slotOf n z.1 with
      | some c =>
        if eqD (gN n OracleName.rleaf (List.ofFn c ++ z.1.rsalt)) (z.1.path.headD default) then 1 else 2
      | none => 9
    else 0
  | _ => 9

theorem which_extSalt :
    (List.range 16).map whichExtSalt = [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem which_slot :
    (List.range 16).map whichSlot = [0, 1, 0, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem which_rsalt :
    (List.range 16).map whichRsalt = [0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  decide +kernel

end OnBytes.Prover.ToyWork
