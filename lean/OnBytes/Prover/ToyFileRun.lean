-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/ToyFileRun.lean: a test: at the small file of OnBytes/TypedOracleCompiler/Joined/ToyFile.lean the
compiled prover (OnBytes/Prover/Defs.lean) is run under 32 families of oracle functions that are not
constant, and the verifier of that file says yes to each string; turned strings are refused
under some of them, as counted.

Why. It holds the prover's text against the verifier's before anything is proved of it: the order of
the roots, the fields of each query, the joining round, the request tree, the openings. The small
file has three joined chains, two trees in one component, a shared round with a tree, two slots.

Main names:
  `gN n`      oracle functions: each answer is a bit of a number made of n and of a code of the
              query
  `σ₀`, `co`  the strategy (chain 1's string holds true everywhere); the coins
  `good n`    the prover returns a string, the interactive verifier accepts the transcript beside
              it, and the compiled verifier says yes to the string, all under gN n
  `all_yes`   good n for all n below 32
  `refusals`, `bent_*`   the same string with one field turned: under how many of the 32 it is
              refused, as counted: the test can fail; unturned: under none
  `explains`, `why_*`   WHY a turned string is accepted where it is: the verifier's value is that of
              a named equation between digests (a collision of a one-bit oracle, or a list that
              reads the same backwards), under each of the 32

Limits: a test, by evaluation. Digests have one bit, so much collides. No round has a test (proof of
work), there are no external strings, no tree is checked by a pruned set of paths: for these see
OnBytes/Prover/ToyWork.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import Compile.MerkleList
import OnBytes.TypedOracleCompiler.Joined.ToyFile
import OnBytes.TypedOracleCompiler.Joined.Verifier
import Rom.Cache

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyFileRun
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Joined.Toy (G D L W F)

/-! ## Codes of queries -/

def bitsN (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + 1 + b.toNat) 0
def digsN (l : List (Dig 1)) : ℕ := l.foldl (fun a d => 2 * a + 1 + (d 0).toNat) 0
def optN : Option Bool → ℕ
  | none => 0
  | some b => 1 + b.toNat

def headN : Head 1 Bool → ℕ
  | .f1 cms x salt => 5 * (digsN cms + 7 * optN x + 31 * bitsN salt)
  | .f2 xl ρ => 5 * (optN xl + 3 * bitsN ρ) + 1
  | .f3 ρ0 c => 5 * (bitsN ρ0 + 17 * bitsN c) + 2
  | .f4 cms r => 5 * (digsN cms + 23 * bitsN r) + 3
  | .f5 ρ0 => 5 * bitsN ρ0 + 4

/-- which round's, and which component's, plain part -/
def pbN : (s : Shape) → (A : RoundSplits s) → PlainPart s A → ℕ
  | [], _, z => nomatch z
  | _ :: _, (_, _), .inl (.inl _) => 0
  | _ :: _, (_, _), .inl (.inr _) => 1
  | _ :: s, (_, A), .inr z => 2 + pbN s A z

def bodyN : Body L → ℕ
  | none => 0
  | some ⟨.inr (.inl (.inl j)), b⟩ => 1 + 2 * j.val + 16 * (show Bool from b).toNat
  | some ⟨.inr (.inl (.inr _)), b⟩ => 5 + 16 * (show Bool from b).toNat
  | some ⟨.inr (.inr (.inr (.inl j))), b⟩ => 7 + 2 * j.val + 16 * (show Bool from b).toNat
  | some _ => 15

/-- a bit of a number made of n and c -/
def mix (n c : ℕ) : Bool :=
  let h1 := ((c + 1) * 2654435761 + (n + 1) * 40503) % 4294967296
  let h2 := ((h1 ^^^ (h1 >>> 15)) * 2246822519) % 4294967296
  (h2 ^^^ (h2 >>> 13)) % 2 == 1
def dg (n c : ℕ) : Dig 1 := fun _ => mix n c

def fbN {t : Tag} (q : FbIn 1 L t) : ℕ :=
  q.round + 6 * headN q.head + 41 * digsN q.rt + 97 * pbN _ _ q.plain

/-- Oracle functions that are not constant. -/
def gN (n : ℕ) : Fam (typedOracleFamily 1 W.K L)
  | .leaf => fun q => dg n (3 + 11 * bodyN q.body + 5 * bitsN q.salt)
  | .node => fun q => dg n (1 + 13 * bitsN q.1 + 29 * bitsN q.2)
  | .rleaf => fun q => dg n (2 + 17 * bitsN q)
  | .rnode => fun q => dg n (4 + 19 * bitsN q.1 + 37 * bitsN q.2)
  | .fb _ => fun q => (fun _ => dg n (fbN q), dg n (fbN q + 1))
  | .fbw _ _ => fun q => (fun _ => dg n (fbN q), dg n (fbN q + 1))
  | .g _ => fun q => dg n (q.round + 3 * bitsN q.ρ + 43 * digsN q.rt + 101 * pbN _ _ q.plain)
  | .ann => fun _ => ()
  | .other => fun _ => dg n 0

/-! ## The run -/

/-- chain 1's string holds true at both places; chain 2's holds false -/
def σ₀ : Strat G.sh Unit :=
  (((), ()), fun _ => (((fun _ => true, false), ()), fun _ => (((), ()), fun _ =>
    ((fun _ => false, ()), fun _ => (((), ()), fun _ => (((), ()), fun _ => ()))))))

def co : Coins 1 L where
  salt := [true, false]
  leaf := fun i b k j => [(i + k + j + b.toNat) % 2 == 1]
  pad := none
  slot := 1
  path := [fun _ => true]
  rsalt := [false, true, true]

def xt : ℕ → TreeK 1 L := fun _ => ⟨fun _ => ⟨none, []⟩, []⟩

def run (n : ℕ) : Res (F.Prf × Tr G.sh) :=
  (proveX F.t F.D.batch F.wq F.embS F.embP F.xin [] true (fun p => p.elim0) xt σ₀ co
    fun _ => 0).det (gN n)

def yes (n : ℕ) (π : F.Prf) : Bool := (F.verify 1 2 [] true π).det (gN n)

def good (n : ℕ) : Bool :=
  match run n with
  | .ok z => yes n z.1 && D.accept true (fun p => p.elim0) z.2
  | _ => false

theorem all_yes : (List.range 32).all good = true := by decide +kernel

/-- under how many of the 32 families the string, turned by f, is refused. (Digests have one bit: a
turned string passes wherever the turned bits collide.) -/
def refusals (f : F.Prf → F.Prf) : ℕ :=
  (List.range 32).countP fun n => match run n with
    | .ok z => !yes n (f z.1)
    | _ => false

theorem bent_none : refusals (fun π => π) = 0 := by decide +kernel
theorem bent_roots : refusals (fun π => { π with roots := π.roots.reverse }) = 14 := by
  decide +kernel
theorem bent_salt : refusals (fun π => { π with salt := [false, false] }) = 7 := by decide +kernel
theorem bent_rtreq : refusals (fun π => { π with rtreq := fun i => !π.rtreq i }) = 32 := by
  decide +kernel
theorem bent_path : refusals (fun π => { π with path := π.path.map fun d i => !d i }) = 20 := by
  decide +kernel
theorem bent_rsalt : refusals (fun π => { π with rsalt := [] }) = 8 := by decide +kernel
theorem bent_slot : refusals (fun π => { π with slot := 0 }) = 10 := by decide +kernel
theorem bent_opens : refusals (fun π => { π with opens := fun _ => none }) = 32 := by decide +kernel

/-! ## Why a turned string is accepted where it is -/

/-- the verifier's value at the string turned by f is crit's (crit sees the string and the turned
one), under each of the 32 -/
def explains (f : F.Prf → F.Prf) (crit : ℕ → F.Prf → F.Prf → Bool) : Bool :=
  (List.range 32).all fun n => match run n with
    | .ok z => yes n (f z.1) == crit n z.1 (f z.1)
    | _ => false

def eqD (a b : Dig 1) : Bool := a 0 == b 0
def rnodeN (n : ℕ) (a b : Dig 1) : Dig 1 := gN n OracleName.rnode (List.ofFn a, List.ofFn b)

/-- what the verifier's chain finds at a string -/
def chainOf (n : ℕ) (π : F.Prf) : Option (Rho G.sh × RootsOfChain 1 G.sh × Phase 1) :=
  (recomputeChainOfProof F.t F.D.batch F.wq F.embP F.xin [] true π).det (gN n)

/-- the climb in the request tree from the string's own data ends in the string's request root -/
def reqCrit (n : ℕ) (π : F.Prf) : Bool :=
  match chainOf n π with
  | some z =>
    match z.2.2.slotVal with
    | some c =>
      eqD (climbF (rnodeN n) π.path π.slot (gN n OracleName.rleaf (List.ofFn c ++ π.rsalt))) π.rtreq
    | none => false
  | none => false

/-- the two places that the small file's verifier reads, as bits: chain 1's block, chain 3's -/
def places (ρ : Rho G.sh) : Bool × Bool := ((G.rho₁ ρ).1 0 0, (G.rho₃ ρ).1 0 0)

/-- the same set of places -/
def sameSet (a b : Bool × Bool) : Bool :=
  (a.1 == b.1 || a.1 == b.2) && (a.2 == b.1 || a.2 == b.2) &&
    (b.1 == a.1 || b.1 == a.2) && (b.2 == a.1 || b.2 == a.2)

/-- the list of roots reversed is accepted exactly where it reads the same backwards -/
theorem why_roots : explains (fun π => { π with roots := π.roots.reverse })
    (fun _ π _ => (π.roots.map fun d => d 0).reverse == π.roots.map fun d => d 0) = true := by
  decide +kernel

/-- another salt of the chain is accepted exactly where the chain then finds the same set of places
read, and a slot value whose climb ends in the request root -/
theorem why_salt : explains (fun π => { π with salt := [false, false] })
    (fun n π π' => match chainOf n π, chainOf n π' with
      | some a, some b => sameSet (places a.1) (places b.1) && reqCrit n π'
      | _, _ => false) = true := by decide +kernel

theorem why_path : explains (fun π => { π with path := π.path.map fun d i => !d i })
    (fun n _ π' => reqCrit n π') = true := by decide +kernel
theorem why_rsalt : explains (fun π => { π with rsalt := [] }) (fun n _ π' =>
    reqCrit n π') = true := by
  decide +kernel
theorem why_slot : explains (fun π => { π with slot := 0 }) (fun n _ π' => reqCrit n
    π') = true := by
  decide +kernel

end OnBytes.Prover.ToyFileRun
