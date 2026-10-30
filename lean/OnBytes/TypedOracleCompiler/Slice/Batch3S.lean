-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3S.lean: THE BATCH's GENERIC PROTOCOL AS A SKELETON (the library's
Twin.PS): THE EVALUABLE VERIFIER verifyP AND thin_verify APPLY TO IT BY DEFINITION. BESIDE
Slice/Batch3.lean, which stands.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY: Batch3 is a InteractiveOracleProof over Round | Shape. A Round holds "its verifier messages are finitely many"
AS DATA; at hash blocks that datum cannot be computed. The library's skeleton (Run/TwinDefs.lean:
RS, PS) keeps it behind a function of Unit, and its evaluable verifier has no parameter of type
Round | Shape. TWO THINGS STOOD IN THE WAY: (i) Batch3's shape is F.r :: (uL C ds₁ ++ …): Twin.up (A
++ B) and Twin.up A ++ Twin.up B are equal by a proof, not by unfolding, at lists that are
variables; (ii) Batch3's (and Plain3's) reads, external reads and decision cut a transcript by Tr |
Rho .fst | .snd and place positions by OPos.left | right, WHICH RECURSE ON SHAPES: at run time a
Shape is a list of Rounds: the datum is forced.
HERE: THE SHAPE IS Twin.up OF A LIST OF SKELETON ROUNDS; EVERY CUT RECURSES ON THE LIST OF ROUNDS'
DATA, WITH A SKELETON TAIL (List RS) AS ITS PARAMETER: NO FUNCTION THAT RUNS HAS A Shape AS A
PARAMETER, AND NONE A WRITTEN ROUND's Round. ofR TAKES A Round, AND THE FIVE ROUNDS THAT D HOLDS
(the front's, the four seams', THE TWO DEAD ONES G.s0 | G.s1 AMONG THEM) ARE BUILT AT EVERY RUN:
"one verifier message" is a proposition: it does not make the datum cheap: LET THEM BE Seam.plain |
Front.one' | Front.silent OF SUCH (their verifier message is Unit); a Seam.written at hash blocks is
untried.
WHOEVER RUNS verifyP AT HASH BLOCKS: HAND early | late IN AS TERMS THAT DO NOT BUILD THE INTERFACE
(not L.early | L.late, as thin_verify's own left side and a file of this project that is not in this
library have them): measured, by the head of another such file.
  MEASURED (in that file): THE FIRST FORM OF THIS FILE RAN OUT OF MEMORY AT HASH BLOCKS: its
    decOS called Plain3's decSeam, WHICH HAS A Shape AS A PARAMETER THAT IT NEVER LOOKS AT: the
    argument is computed all the same. With decSeamS (a skeleton tail) it runs; with decSeam put
    back it runs out of memory again. shdS stands in the place of the library's RAnn.ofShared .sh
    r.up (a Round as its parameter) FOR THE SAME REASON; at the toy, whose one shared round draws
    nothing, RAnn.ofShared did NOT bite: that it bites at a shared round that draws is a thought.
  ofR r              a round as a skeleton round ((ofR r).up is r by unfolding): for the front and
    the seams, whose verifier messages are one
  shdS r, shdS_eq    "only the shared part is sent", from the skeleton round; it IS RAnn.ofShared
    .sh r.up by unfolding;   decSeamS: a seam in front adds no position, with a skeleton tail
  shA C T ds         Twin.up (SL C ds ++ T): written rounds before a skeleton tail
  trF | trS, rhF | rhS, plF | plS, poL | poR     the two parts of a transcript, of verifier
    messages, of plain parts; a position of either part as a position of the whole; rho_trF |
    rho_trS, plains_trF | plains_trS, read_poL | read_poR: their laws
  BD.S₃, BD.SJ, BD.S      the skeleton: front | first stretch | THE JOINING ROUND | second
    stretch | seam | third stretch: Batch3's rounds, one for one
  BD.t₁ t₂ t₃, r₁ r₂ r₃, i₁ i₂ i₃   the three stretches of a transcript, of verifier messages; a
    stretch's position in the whole
  BD.asksS, BD.posS, BD.ownS  what the verifier messages ask for (Plain3's asksL at the three
    stretches); where a tree's position lies
  BD.annS            the annotation: Batch3's, round for round
  BatchPS D dec : PS X (one stored table)    THE SKELETON: the verifier reads every position of
    the front and what the draws ask for; it accepts by PLAIN3's OWN accOn on the three stretches,
    with dec at the instance, the front's symbols and plain part
  batchPS_local  (BatchPS D dec).up.loc is local, for every decision (after plain3_local's text,
    over its own okOn_congr | viewOn_congr)
  annS_coherent, annS_localTo
(BatchPS D dec).up = BatchP D dec IS NOT SHOWN IN THIS LIBRARY [a BatchInteractiveOracleProof
holds its shape as a field]. WHOEVER WANTS TO RUN BUILDS ON THIS ONE; whoever proves soundness at
BatchP has it of this one only with that equation.
WHAT IS NOT SAID. verifyP IS, BY THE LIBRARY's OWN HEAD AND MEASURE, NOT THE FORM THAT COMES HOME
WITH A REAL HASH (Run/ThinBits.lean's head): the three later forms (verifyPB | verifyPR | verifyPX)
are general in a skeleton: not said over the sibling. The wiring: Slice/Batch3SWire.lean. That
anything runs at size.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run
open _root_.Run.Twin (RS PS)

/-- a round as a skeleton round -/
@[reducible] def ofR (r : Round) : RS where
  Orc := r.Orc
  Pos := r.Pos
  Sym := r.Sym
  rd := r.rd
  Plain := r.Plain
  Chal := r.Chal
  dOrc := r.dOrc
  dPlain := r.dPlain
  finT := fun _ => r.finChal
  ne := r.neChal

theorem ofR_up (r : Round) : (ofR r).up = r := rfl

/-- a shared round in which only the shared part is sent: the library's RAnn.ofShared .sh, FROM THE
SKELETON ROUND (that has a Round as its parameter: at run time the datum would be forced) -/
@[reducible] def shdS (r : RS) : RAnn r.up where
  kind := .sh
  M0 := r.Orc × r.Plain
  Mj := Unit
  split := (Equiv.prodPUnit (r.Orc × r.Plain)).symm
  P0 := r.Plain
  Pj := Unit
  pl0 := fun m => m.2
  plj := fun _ => ()
  plain := (Equiv.prodPUnit r.Plain).symm
  own := fun _ => false

theorem shdS_eq (r : RS) : shdS r = RAnn.ofShared .sh r.up := rfl

/-- a seam in front adds no position: decSeam WITH A SKELETON TAIL in the place of a Shape -/
def decSeamS (s : Seam) (T : List RS) (h : DecidableEq (OPos (_root_.Run.Twin.up T))) :
    DecidableEq (OPos (_root_.Run.Twin.up (ofR s.r :: T))) := by
  haveI := h
  haveI : DecidableEq s.r.Pos := fun p _ => (s.noPos.false p).elim
  exact inferInstanceAs (DecidableEq (s.r.Pos ⊕ OPos (_root_.Run.Twin.up T)))

/-! ## Written rounds before a skeleton tail -/

section Kit
variable (C : PQ.CK) (T : List RS)

/-- written rounds before a skeleton tail -/
abbrev shA (ds : List PQ.RD) : Shape := _root_.Run.Twin.up (PQ.SL C ds ++ T)

def trF : (ds : List PQ.RD) → Tr (shA C T ds) → Tr (PQ.uL C ds)
  | [], _ => ()
  | _ :: ds, (m, c, a) => (m, c, trF ds a)
def trS : (ds : List PQ.RD) → Tr (shA C T ds) → Tr (_root_.Run.Twin.up T)
  | [], a => a
  | _ :: ds, (_, _, a) => trS ds a
def rhF : (ds : List PQ.RD) → Rho (shA C T ds) → Rho (PQ.uL C ds)
  | [], _ => ()
  | _ :: ds, (c, a) => (c, rhF ds a)
def rhS : (ds : List PQ.RD) → Rho (shA C T ds) → Rho (_root_.Run.Twin.up T)
  | [], a => a
  | _ :: ds, (_, a) => rhS ds a
def plF : (ds : List PQ.RD) → Plains (shA C T ds) → Plains (PQ.uL C ds)
  | [], _ => ()
  | _ :: ds, (c, a) => (c, plF ds a)
def plS : (ds : List PQ.RD) → Plains (shA C T ds) → Plains (_root_.Run.Twin.up T)
  | [], a => a
  | _ :: ds, (_, a) => plS ds a
def poL : (ds : List PQ.RD) → OPos (PQ.uL C ds) → OPos (shA C T ds)
  | [], p => p.elim
  | _ :: _, .inl p => .inl p
  | _ :: ds, .inr q => .inr (poL ds q)
def poR : (ds : List PQ.RD) → OPos (_root_.Run.Twin.up T) → OPos (shA C T ds)
  | [], q => q
  | _ :: ds, q => .inr (poR ds q)

theorem rho_trF : ∀ (ds : List PQ.RD) (τ : Tr (shA C T ds)), (trF C T ds τ).rho = rhF C T ds τ.rho
  | [], _ => rfl
  | _ :: ds, (_, c, a) => congrArg (Prod.mk c) (rho_trF ds a)
theorem rho_trS : ∀ (ds : List PQ.RD) (τ : Tr (shA C T ds)), (trS C T ds τ).rho = rhS C T ds τ.rho
  | [], _ => rfl
  | _ :: ds, (_, _, a) => rho_trS ds a
theorem plains_trF : ∀ (ds : List PQ.RD) (τ : Tr (shA C T ds)),
    (trF C T ds τ).plains = plF C T ds τ.plains
  | [], _ => rfl
  | _ :: ds, (m, _, a) => congrArg (Prod.mk m.2) (plains_trF ds a)
theorem plains_trS : ∀ (ds : List PQ.RD) (τ : Tr (shA C T ds)),
    (trS C T ds τ).plains = plS C T ds τ.plains
  | [], _ => rfl
  | _ :: ds, (_, _, a) => plains_trS ds a

/-- two transcripts agree at a position of the written rounds if and only if their first parts agree
there -/
theorem read_poL : ∀ (ds : List PQ.RD) (τ τ' : Tr (shA C T ds)) (p : OPos (PQ.uL C ds)),
    τ.read (poL C T ds p) = τ'.read (poL C T ds p) ↔ (trF C T ds τ).read p = (trF C T ds τ').read p
  | [], _, _, p => p.elim
  | _ :: _, (_, _, _), (_, _, _), .inl _ => Iff.rfl
  | _ :: ds, (_, _, a), (_, _, a'), .inr q => read_poL ds a a' q

/-- and at a position of the tail if and only if their second parts agree there -/
theorem read_poR : ∀ (ds : List PQ.RD) (τ τ' : Tr (shA C T ds)) (q : OPos (_root_.Run.Twin.up T)),
    τ.read (poR C T ds q) = τ'.read (poR C T ds q) ↔ (trS C T ds τ).read q = (trS C T ds τ').read q
  | [], _, _, _ => Iff.rfl
  | _ :: ds, (_, _, a), (_, _, a'), q => read_poR ds a a' q

/-- equality of positions can be decided, if it can in the tail -/
def decA (h : DecidableEq (OPos (_root_.Run.Twin.up T))) : (ds : List PQ.RD) →
    DecidableEq (OPos (shA C T ds))
  | [] => h
  | d :: ds => by
      haveI := decA h ds
      haveI := PQ.decPosT d.trees
      exact inferInstanceAs (DecidableEq (PQ.PosT d.trees ⊕ OPos (shA C T ds)))

/-- written rounds, all local, before what follows -/
def annLoS (At : RoundSplits (_root_.Run.Twin.up T)) : (ds : List PQ.RD) → RoundSplits (shA C T ds)
  | [] => At
  | d :: ds => ((PQ.roundS C d).lo, annLoS At ds)

/-- written rounds, all shared: only the shared part is sent -/
def annShS (At : RoundSplits (_root_.Run.Twin.up T)) : (ds : List PQ.RD) → RoundSplits (shA C T ds)
  | [] => At
  | d :: ds => (shdS (PQ.roundS C d), annShS At ds)

theorem annLoS_coherent (At : RoundSplits (_root_.Run.Twin.up T)) (h : At.Coherent) : ∀ ds : List PQ.RD,
    (annLoS C T At ds).Coherent
  | [] => h
  | _ :: ds => ⟨RAnn.ofSlot_coherent _ _, annLoS_coherent At h ds⟩

theorem annShS_coherent (At : RoundSplits (_root_.Run.Twin.up T)) (h : At.Coherent) : ∀ ds : List PQ.RD,
    (annShS C T At ds).Coherent
  | [] => h
  | _ :: ds => ⟨RAnn.ofShared_coherent _ _, annShS_coherent At h ds⟩

theorem annLoS_localTo (At : RoundSplits (_root_.Run.Twin.up T)) :
    ∀ (ds : List PQ.RD) (n : ℕ), n < ds.length → RoundSplits.LocalTo n (shA C T ds) (annLoS C T At ds)
  | _ :: _, 0, _ => rfl
  | _ :: ds, n + 1, h => ⟨rfl, annLoS_localTo At ds n (Nat.lt_of_succ_lt_succ h)⟩

end Kit

/-! ## The skeleton -/

namespace BD
variable (D : BD)

/-- the local seam behind the shared block, and the third stretch -/
abbrev S₃ : List RS := ofR D.G.s3.r :: PQ.SL D.G.C D.G.ds₃
/-- THE JOINING ROUND, the second stretch, and what follows -/
abbrev SJ : List RS := ofR D.G.s2.r :: (PQ.SL D.G.C D.G.ds₂ ++ D.S₃)
/-- The skeleton's rounds: front, first stretch, JOINING ROUND, second stretch, seam, third
stretch. -/
abbrev S : List RS := ofR D.F.r :: (PQ.SL D.G.C D.G.ds₁ ++ D.SJ)
abbrev shS : Shape := _root_.Run.Twin.up D.S

instance decOS : DecidableEq (OPos D.shS) := by
  haveI := D.F.pt.decPos
  haveI : DecidableEq (OPos (_root_.Run.Twin.up D.S₃)) :=
      decSeamS D.G.s3 (PQ.SL D.G.C D.G.ds₃) (PQ.decSL D.G.C D.G.ds₃)
  haveI : DecidableEq (OPos (_root_.Run.Twin.up D.SJ)) :=
      decSeamS D.G.s2 (PQ.SL D.G.C D.G.ds₂ ++ D.S₃) (decA D.G.C D.S₃ inferInstance D.G.ds₂)
  haveI : DecidableEq (OPos (shA D.G.C D.SJ D.G.ds₁)) := decA D.G.C D.SJ inferInstance D.G.ds₁
  exact inferInstanceAs (DecidableEq (D.F.r.Pos ⊕ OPos (shA D.G.C D.SJ D.G.ds₁)))

/-- the three stretches of a transcript -/
def t₁ (τ : Tr D.shS) : Tr (PQ.uL D.G.C D.G.ds₁) := trF D.G.C D.SJ D.G.ds₁ τ.2.2
def tJ (τ : Tr D.shS) : Tr (shA D.G.C D.S₃ D.G.ds₂) := (trS D.G.C D.SJ D.G.ds₁ τ.2.2).2.2
def t₂ (τ : Tr D.shS) : Tr (PQ.uL D.G.C D.G.ds₂) := trF D.G.C D.S₃ D.G.ds₂ (D.tJ τ)
def t₃ (τ : Tr D.shS) : Tr (PQ.uL D.G.C D.G.ds₃) := (trS D.G.C D.S₃ D.G.ds₂ (D.tJ τ)).2.2
/-- the three stretches of the verifier messages -/
def r₁ (ρ : Rho D.shS) : Rho (PQ.uL D.G.C D.G.ds₁) := rhF D.G.C D.SJ D.G.ds₁ ρ.2
def rJ (ρ : Rho D.shS) : Rho (shA D.G.C D.S₃ D.G.ds₂) := (rhS D.G.C D.SJ D.G.ds₁ ρ.2).2
def r₂ (ρ : Rho D.shS) : Rho (PQ.uL D.G.C D.G.ds₂) := rhF D.G.C D.S₃ D.G.ds₂ (D.rJ ρ)
def r₃ (ρ : Rho D.shS) : Rho (PQ.uL D.G.C D.G.ds₃) := (rhS D.G.C D.S₃ D.G.ds₂ (D.rJ ρ)).2
/-- a stretch's position as a position of the whole -/
def i₁ (p : OPos (PQ.uL D.G.C D.G.ds₁)) : OPos D.shS := .inr (poL D.G.C D.SJ D.G.ds₁ p)
def iJ (p : OPos (shA D.G.C D.S₃ D.G.ds₂)) : OPos D.shS := .inr (poR D.G.C D.SJ D.G.ds₁ (.inr p))
def i₂ (p : OPos (PQ.uL D.G.C D.G.ds₂)) : OPos D.shS := D.iJ (poL D.G.C D.S₃ D.G.ds₂ p)
def i₃ (p : OPos (PQ.uL D.G.C D.G.ds₃)) : OPos D.shS := D.iJ (poR D.G.C D.S₃ D.G.ds₂ (.inr p))

theorem rho_t₁ (τ : Tr D.shS) : (D.t₁ τ).rho = D.r₁ τ.rho := rho_trF D.G.C D.SJ D.G.ds₁ τ.2.2
theorem rho_tJ (τ : Tr D.shS) : (D.tJ τ).rho = D.rJ τ.rho :=
  congrArg Prod.snd (rho_trS D.G.C D.SJ D.G.ds₁ τ.2.2)
theorem rho_t₂ (τ : Tr D.shS) : (D.t₂ τ).rho = D.r₂ τ.rho := by
  unfold t₂ r₂
  rw [rho_trF, D.rho_tJ]
theorem rho_t₃ (τ : Tr D.shS) : (D.t₃ τ).rho = D.r₃ τ.rho := by
  unfold t₃ r₃
  rw [← D.rho_tJ, ← rho_trS]
  rfl

theorem plains_t₁ (τ τ' : Tr D.shS) (h : τ.plains = τ'.plains) :
    (D.t₁ τ).plains = (D.t₁ τ').plains := by
  unfold t₁
  rw [plains_trF, plains_trF, show τ.2.2.plains = τ'.2.2.plains from congrArg Prod.snd h]
theorem plains_tJ (τ τ' : Tr D.shS) (h : τ.plains = τ'.plains) :
    (D.tJ τ).plains = (D.tJ τ').plains := by
  have e : (trS D.G.C D.SJ D.G.ds₁ τ.2.2).plains = (trS D.G.C D.SJ D.G.ds₁ τ'.2.2).plains := by
    rw [plains_trS, plains_trS, show τ.2.2.plains = τ'.2.2.plains from congrArg Prod.snd h]
  exact congrArg Prod.snd e
theorem plains_t₂ (τ τ' : Tr D.shS) (h : τ.plains = τ'.plains) :
    (D.t₂ τ).plains = (D.t₂ τ').plains := by
  unfold t₂
  rw [plains_trF, plains_trF, D.plains_tJ τ τ' h]
theorem plains_t₃ (τ τ' : Tr D.shS) (h : τ.plains = τ'.plains) :
    (D.t₃ τ).plains = (D.t₃ τ').plains := by
  have e : (trS D.G.C D.S₃ D.G.ds₂ (D.tJ τ)).plains = (trS D.G.C D.S₃ D.G.ds₂ (D.tJ τ')).plains :=
      by
    rw [plains_trS, plains_trS, D.plains_tJ τ τ' h]
  exact congrArg Prod.snd e

theorem read_i₁ (τ τ' : Tr D.shS) (p : OPos (PQ.uL D.G.C D.G.ds₁)) :
    τ.read (D.i₁ p) = τ'.read (D.i₁ p) ↔ (D.t₁ τ).read p = (D.t₁ τ').read p :=
  read_poL D.G.C D.SJ D.G.ds₁ τ.2.2 τ'.2.2 p
theorem read_iJ (τ τ' : Tr D.shS) (p : OPos (shA D.G.C D.S₃ D.G.ds₂)) :
    τ.read (D.iJ p) = τ'.read (D.iJ p) ↔ (D.tJ τ).read p = (D.tJ τ').read p :=
  read_poR D.G.C D.SJ D.G.ds₁ τ.2.2 τ'.2.2 (.inr p)
theorem read_i₂ (τ τ' : Tr D.shS) (p : OPos (PQ.uL D.G.C D.G.ds₂)) :
    τ.read (D.i₂ p) = τ'.read (D.i₂ p) ↔ (D.t₂ τ).read p = (D.t₂ τ').read p :=
  (D.read_iJ τ τ' _).trans (read_poL D.G.C D.S₃ D.G.ds₂ (D.tJ τ) (D.tJ τ') p)
theorem read_i₃ (τ τ' : Tr D.shS) (p : OPos (PQ.uL D.G.C D.G.ds₃)) :
    τ.read (D.i₃ p) = τ'.read (D.i₃ p) ↔ (D.t₃ τ).read p = (D.t₃ τ').read p :=
  (D.read_iJ τ τ' _).trans (read_poR D.G.C D.S₃ D.G.ds₂ (D.tJ τ) (D.tJ τ') (.inr p))

/-- what the verifier messages of a whole run ask for: Plain3's asksL at the three stretches -/
def asksS (ρ : Rho D.shS) : List Ask :=
  asksL D.G.a D.G.all D.G.xs₁ 0 D.G.ds₁ (PQ.drawnSL D.G.C D.G.ds₁ (D.r₁ ρ)) ++
    (asksL D.G.a D.G.all D.G.xs₂ 0 D.G.ds₂ (PQ.drawnSL D.G.C D.G.ds₂ (D.r₂ ρ)) ++
      asksL D.G.a D.G.all D.G.xs₃ 0 D.G.ds₃ (PQ.drawnSL D.G.C D.G.ds₃ (D.r₃ ρ)))

/-- position x of tree n as a position of the shape -/
def posS (n x : ℕ) : Option (OPos D.shS) :=
  if n < nTrees D.G.ds₁ then (PQ.posAtS D.G.C D.G.ds₁ n x).map D.i₁
  else if n - nTrees D.G.ds₁ < nTrees D.G.ds₂ then (PQ.posAtS D.G.C D.G.ds₂
      (n - nTrees D.G.ds₁) x).map D.i₂
  else (PQ.posAtS D.G.C D.G.ds₃ (n - nTrees D.G.ds₁ - nTrees D.G.ds₂) x).map D.i₃

def ownS : Ask → Option (OPos D.shS)
  | .stored _ _ => none
  | .own n x => D.posS n x

/-- the front's symbols in a transcript -/
def frontS (τ : Tr D.shS) : (p : D.F.r.Pos) → D.F.r.Sym p := fun p => D.F.r.rd τ.1.1 p

/-- all positions of the front -/
def frontPosS : Finset (OPos D.shS) := (@Finset.univ _ D.F.pt.finPos).image Sum.inl

theorem col_congrS (τ τ' : Tr D.shS) (n x : ℕ) (h : ∀ p, D.posS n x = some p →
    τ.read p = τ'.read p) :
    D.G.col (D.t₁ τ) (D.t₂ τ) (D.t₃ τ) n x = D.G.col (D.t₁ τ') (D.t₂ τ') (D.t₃ τ') n x := by
  unfold Stretches.col
  unfold posS at h
  by_cases h1 : n < nTrees D.G.ds₁
  · rw [if_pos h1, if_pos h1]
    rw [if_pos h1] at h
    exact PQ.colAtS_congr D.G.C D.G.ds₁ _ _ _ _ fun p hp =>
        (D.read_i₁ τ τ' p).1 (h _ (by rw [hp]; rfl))
  · rw [if_neg h1, if_neg h1]
    rw [if_neg h1] at h
    by_cases h2 : n - nTrees D.G.ds₁ < nTrees D.G.ds₂
    · rw [if_pos h2, if_pos h2]
      rw [if_pos h2] at h
      exact PQ.colAtS_congr D.G.C D.G.ds₂ _ _ _ _ fun p hp =>
          (D.read_i₂ τ τ' p).1 (h _ (by rw [hp]; rfl))
    · rw [if_neg h2, if_neg h2]
      rw [if_neg h2] at h
      exact PQ.colAtS_congr D.G.C D.G.ds₃ _ _ _ _ fun p hp =>
          (D.read_i₃ τ τ' p).1 (h _ (by rw [hp]; rfl))

/-- the annotation: Batch3's, round for round -/
def annS₃ : RoundSplits (_root_.Run.Twin.up D.S₃) := _root_.Run.Twin.allLo D.S₃
def annSJ : RoundSplits (_root_.Run.Twin.up D.SJ) := (D.aJ, annShS D.G.C D.S₃ D.annS₃ D.G.ds₂)
def annS : RoundSplits D.shS := ((ofR D.F.r).lo, annLoS D.G.C D.SJ D.annSJ D.G.ds₁)

theorem annS_coherent (hJ : D.aJ.Coherent) : D.annS.Coherent :=
  And.intro (RAnn.ofSlot_coherent _ _)
    (annLoS_coherent D.G.C D.SJ D.annSJ
      (And.intro hJ (annShS_coherent D.G.C D.S₃ D.annS₃
        (by unfold annS₃; rw [_root_.Run.Twin.allLo_eq]; exact BatchOne.BAnn.allLocal_coherent _) D.G.ds₂)) D.G.ds₁)

/-- the front and the first stretch are local: up to every round number n ≤ the first stretch's
length -/
theorem annS_localTo : ∀ n, n ≤ D.G.ds₁.length → RoundSplits.LocalTo n D.shS D.annS
  | 0, _ => rfl
  | n + 1, h => ⟨rfl, annLoS_localTo D.G.C D.SJ D.annSJ D.G.ds₁ n h⟩

end BD

/-- THE SKELETON OF THE BATCH's GENERIC PROTOCOL. -/
@[reducible] def BatchPS {X : Type} (D : BD)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    PS X (oneExternalString (2 ^ D.G.a) PQ.SgX) where
  S := D.S
  blinded := fun _ => true
  extReads := fun _ ρ => ((D.asksS ρ).filterMap (Ask.ext D.G.a)).toFinset
  reads := fun _ ρ _ => D.frontPosS ∪ ((D.asksS ρ).filterMap D.ownS).toFinset
  accept := fun x y τ => D.G.accOn y (D.t₁ τ) (D.t₂ τ) (D.t₃ τ) (dec x (D.frontS τ) τ.1.2)
  ann := D.annS

/-- The verifier is local, for every decision. -/
theorem batchPS_local {X : Type} (D : BD)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    (BatchPS D dec).up.loc.IsLocal := by
  intro x y y' τ τ' hρ hp he hr
  have hf : D.frontS τ = D.frontS τ' := funext fun p =>
    hr (Sum.inl p) (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (@Finset.mem_univ _ D.F.pt.finPos p)))
  have hq : τ.1.2 = τ'.1.2 := congrArg Prod.fst hp
  have he' : ∀ q ∈ D.asksS τ.rho, ∀ p, Ask.ext D.G.a q = some p → y p = y' p := fun q hq p h =>
    he p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨q, hq, h⟩))
  have hc : ∀ n x, Ask.own n x ∈ D.asksS τ.rho →
      D.G.col (D.t₁ τ) (D.t₂ τ) (D.t₃ τ) n x = D.G.col (D.t₁ τ') (D.t₂ τ') (D.t₃ τ') n x :=
    fun n x hq => D.col_congrS τ τ' n x fun p h =>
      hr p (Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hq, h⟩)))
  have r1 : (D.t₁ τ).rho = (D.t₁ τ').rho := by rw [D.rho_t₁, D.rho_t₁, hρ]
  have r2 : (D.t₂ τ).rho = (D.t₂ τ').rho := by rw [D.rho_t₂, D.rho_t₂, hρ]
  have r3 : (D.t₃ τ).rho = (D.t₃ τ').rho := by rw [D.rho_t₃, D.rho_t₃, hρ]
  have m1 : ∀ q ∈ asksL D.G.a D.G.all D.G.xs₁ 0 D.G.ds₁ (drOn D.G.C D.G.ds₁ (D.t₁ τ)),
      q ∈ D.asksS τ.rho :=
    fun q hq => by
      unfold drOn at hq
      rw [PQ.rhoS_eq, D.rho_t₁] at hq
      exact List.mem_append_left _ hq
  have m2 : ∀ q ∈ asksL D.G.a D.G.all D.G.xs₂ 0 D.G.ds₂ (drOn D.G.C D.G.ds₂ (D.t₂ τ)),
      q ∈ D.asksS τ.rho :=
    fun q hq => by
      unfold drOn at hq
      rw [PQ.rhoS_eq, D.rho_t₂] at hq
      exact List.mem_append_right _ (List.mem_append_left _ hq)
  have m3 : ∀ q ∈ asksL D.G.a D.G.all D.G.xs₃ 0 D.G.ds₃ (drOn D.G.C D.G.ds₃ (D.t₃ τ)),
      q ∈ D.asksS τ.rho :=
    fun q hq => by
      unfold drOn at hq
      rw [PQ.rhoS_eq, D.rho_t₃] at hq
      exact List.mem_append_right _ (List.mem_append_right _ hq)
  show D.G.accOn y (D.t₁ τ) (D.t₂ τ) (D.t₃ τ) (dec x (D.frontS τ) τ.1.2) =
    D.G.accOn y' (D.t₁ τ') (D.t₂ τ') (D.t₃ τ') (dec x (D.frontS τ') τ'.1.2)
  rw [← hf, ← hq]
  unfold Stretches.accOn Stretches.view₁ Stretches.view₂ Stretches.view₃
  rw [okOn_congr D.G.C D.G.a D.G.all D.G.ds₁ D.G.xs₁ y y' _ _ r1 fun q hq => he' q (m1 q hq),
    okOn_congr D.G.C D.G.a D.G.all D.G.ds₂ D.G.xs₂ y y' _ _ r2 fun q hq => he' q (m2 q hq),
    okOn_congr D.G.C D.G.a D.G.all D.G.ds₃ D.G.xs₃ y y' _ _ r3 fun q hq => he' q (m3 q hq),
    viewOn_congr D.G.C D.G.a D.G.all D.G.ds₁ D.G.xs₁ y y' _ _ D.G.key₁ _ _ r1 (D.plains_t₁ τ τ' hp)
      (fun q hq => he' q (m1 q hq)) fun n x hq => hc n x (m1 _ hq),
    viewOn_congr D.G.C D.G.a D.G.all D.G.ds₂ D.G.xs₂ y y' _ _ D.G.key₂ _ _ r2 (D.plains_t₂ τ τ' hp)
      (fun q hq => he' q (m2 q hq)) fun n x hq => hc n x (m2 _ hq),
    viewOn_congr D.G.C D.G.a D.G.all D.G.ds₃ D.G.xs₃ y y' _ _ D.G.key₃ _ _ r3 (D.plains_t₃ τ τ' hp)
      (fun q hq => he' q (m3 q hq)) fun n x hq => hc n x (m3 _ hq)]

end TypedOracleCompiler.Slice
