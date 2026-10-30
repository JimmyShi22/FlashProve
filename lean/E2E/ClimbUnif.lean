-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbUnif.lean: when a pair with bits (E2E/ClimbPair.lean) keeps probabilities, and that the
pairs of the typed rounds, of a file and of the link do.

A pair between the lists of rounds s and t has a map `old` from the verifier messages of t back to
those of s. Its laws fix `old` on the verifier messages that pass the test and leave it free on the
others. So they do not say that the old part of a uniform verifier message of t is uniform in s.
`Pair.Unif` asks that, round by round.

  `Pair.Unif p`: in each round, `old` maps the uniform distribution on t's verifier messages to the
    uniform distribution on s's.
  `Pair.map_oldR_unif`, `Pair.prRho_old`: then `oldR` (E2E/ClimbRun.lean) maps the uniform verifier
    randomness of t to that of s, and a set of verifier randomness of s has the probability of the
    set of those of t whose old part lies in it.
  `Honest.prRho_withheld_up`: so the abort set of an honest prover carried up has the probability of
    the abort set that it came from.
  `Pair.prRho_zeroR`: for EVERY set B of verifier randomness of t, the set {ρ | zeroR ρ ∈ B} of s
    has the probability of {ρ' | zeroR (oldR ρ') ∈ B} in t. `Pair.prRho_zeroR_le`: for a blind set
    (`Pair.BlindSet`, E2E/ClimbRun.lean) that is at most the probability of B.
    `Honest.prRho_withheld_dn_le`: so the abort set of a blind prover carried down has at most the
    probability of the prover's own.
  `Pair.cons_unif`, `Pair.app_unif`, `pair3_unif`: a round kept as it is, two pairs in a row, three
    chains.
  `rpZ_unif`, `pairZ_unif`, `pairT_unif`, `pairW_unif`, `pairL_unif`: a typed round with proof of
    work against the round without, a list of such rounds, a chain of a file, a file's three chains,
    the link. They hold at every kit
    that does not read an entry's proof of work (`KitFree`) and at all rounds' data.

Limits.
  * The probability of {ρ | zeroR ρ ∈ B} is tied to that of B ITSELF for blind sets alone. (By
    counting, and no theorem here: if every member of B passes, the first is the second times the
    number of values of t's verifier randomness over that of s's.)
  * Nothing on the probability that all verifier messages pass.
  * The verifier randomness of one run of one protocol. The joint randomness of a batch, in which a
    shared verifier message stands once for all requests, is not treated.
  * No abort set is bounded here, and no honest prover is written.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbRun
import E2E.ClimbWhole
import E2E.ClimbLink

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open OnBytes.Maker
open Compile.Joined (plainRound)
open TypedOracleCompiler.Run.PQ (RD roundS SOf)
open _root_.Run.PQ (CK s0)

/-! ## 1. The predicate and the law -/

/-- Round by round, the old part of a uniform verifier message of t is a uniform verifier message of
s. -/
def Pair.Unif : {s t : Iop.Shape} → Pair s t → Prop
  | [], [], _ => True
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | r :: _, r' :: _, (u, p) => (unif r'.Chal).map u.old = unif r.Chal ∧ Pair.Unif p

/-- The old part of uniform verifier randomness of t is uniform verifier randomness of s. -/
theorem Pair.map_oldR_unif :
    ∀ {s t : Iop.Shape} (p : Pair s t), p.Unif → (unif (Rho t)).map p.oldR = unif (Rho s)
  | [], [], _, _ => PMF.map_id _
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | r :: s, r' :: t, (u, p), h =>
    map_unif_prodMap (Ω₁ := r'.Chal) (Ω₂ := Rho t) (Y₁ := r.Chal) (Y₂ := Rho s) u.old p.oldR h.1
      (Pair.map_oldR_unif p h.2)

/-- **A set of verifier randomness of s has the probability of the set of those of t whose old part
lies in it.** -/
theorem Pair.prRho_old {s t : Iop.Shape} (p : Pair s t) (h : p.Unif) (A : Set (Rho s)) :
    prRho {ρ' : Rho t | p.oldR ρ' ∈ A} = prRho A := by
  unfold prRho
  rw [← Pair.map_oldR_unif p h, pr_map]
  rfl

/-- The abort set of an honest prover carried up has the probability of the one that it came
from. -/
theorem Honest.prRho_withheld_up {X : Type} {E : ExtSpec} {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P)
    (h : S.pair.Unif) {Wt : Type} (H : Honest P₀ Wt) (w : Wt) (x : X) :
    prRho ((Honest.up S H).withheld w x) = prRho (H.withheld w x) :=
  Pair.prRho_old S.pair h (H.withheld w x)

/-- **For every set B of verifier randomness of t: the verifier randomness of s whose image lies in
B has the probability of the verifier randomness of t the image of whose old part lies in B.** No
blindness is asked. -/
theorem Pair.prRho_zeroR {s t : Iop.Shape} (p : Pair s t) (h : p.Unif) (B : Set (Rho t)) :
    prRho {ρ' : Rho t | p.zeroR (p.oldR ρ') ∈ B} = prRho {ρ : Rho s | p.zeroR ρ ∈ B} :=
  Pair.prRho_old p h {ρ | p.zeroR ρ ∈ B}

/-- For a blind set that is at most the probability of B itself. -/
theorem Pair.prRho_zeroR_le {s t : Iop.Shape} (p : Pair s t) (h : p.Unif) (B : Set (Rho t))
    (hb : p.BlindSet B) : prRho {ρ : Rho s | p.zeroR ρ ∈ B} ≤ prRho B := by
  rw [← Pair.prRho_zeroR p h B]
  exact pr_mono _ fun ρ' hρ => hb ρ' hρ

/-- **The abort set of a blind prover carried down has at most the probability of the prover's
own.** So a bound on the abort set of a blind prover of P, under P's own verifier randomness, bounds
the abort set that stands beside `Honest.Acc` at P₀. -/
theorem Honest.prRho_withheld_dn_le {X : Type} {E : ExtSpec} {P₀ P : InteractiveOracleProof X E}
    (S : ProtoPair P₀ P) (h : S.pair.Unif) {Wt : Type} (H' : Honest P Wt) (hb : Blind S H') (w : Wt)
    (x : X) : prRho ((Honest.dn S H').withheld w x) ≤ prRho (H'.withheld w x) :=
  Pair.prRho_zeroR_le S.pair h (H'.withheld w x) (hb w x)

/-! ## 2. Putting pairs together -/

/-- One more round in front, kept as it is. -/
theorem Pair.cons_unif (r : Round) {s t : Iop.Shape} {p : Pair s t} (h : p.Unif) :
    (Pair.cons r p).Unif :=
  ⟨PMF.map_id _, h⟩

/-- Two pairs in a row. -/
theorem Pair.app_unif :
    ∀ {s t s' t' : Iop.Shape} {p : Pair s t} {p' : Pair s' t'},
      p.Unif → p'.Unif → (Pair.app p p').Unif
  | [], [], _, _, _, _, _, h' => h'
  | [], _ :: _, _, _, p, _, _, _ => Empty.elim p
  | _ :: _, [], _, _, p, _, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (_, _), _, h, h' => ⟨h.1, Pair.app_unif h.2 h'⟩

/-- Three chains with a round in front of each. -/
theorem pair3_unif (rF rJ r3 : Round) {s₁ t₁ s₂ t₂ s₃ t₃ : Iop.Shape} {p₁ : Pair s₁ t₁}
    {p₂ : Pair s₂ t₂} {p₃ : Pair s₃ t₃} (h₁ : p₁.Unif) (h₂ : p₂.Unif) (h₃ : p₃.Unif) :
    (pair3 rF rJ r3 p₁ p₂ p₃).Unif :=
  Pair.cons_unif rF (Pair.app_unif h₁ (Pair.cons_unif rJ (Pair.app_unif h₂
    (Pair.cons_unif r3 h₃))))

/-! ## 3. The typed rounds, a file, the link -/

variable (C : CK) (K : KitFree C)

/-- One typed round: dropping the proof-of-work bits of a uniform verifier message, and going back
through the kit's bijection, gives a uniform verifier message of the round without proof of
work. -/
theorem rpZ_unif (d : RD) :
    (unif (roundS C d).up.Chal).map (rpZ C K d).old = unif (roundS C (rd0 d)).up.Chal :=
  (PMF.map_comp (GChal.old (b := d.entry.work)) (unif (GChal d.entry.work (C.Ch d.entry d.kind)))
      (K.eqv d.entry d.kind).symm).symm.trans
    ((congrArg (PMF.map (K.eqv d.entry d.kind).symm)
        (GChal.map_old_unif d.entry.work (C.Ch d.entry d.kind))).trans
      (map_unif_equiv (K.eqv d.entry d.kind).symm))

theorem pairZ_unif : ∀ {l₀ l : List RD} (z : Z0 l₀ l), (pairZ C K z).Unif
  | _, _, .nil => trivial
  | _, _, .cons d z => ⟨rpZ_unif C K d, pairZ_unif z⟩

/-- A chain of a file. -/
theorem pairT_unif (ds : List RDT) : (pairT C K ds).Unif := pairZ_unif C K (z0T ds)

/-- A file's three chains with the front round, the joining round and the seam. -/
theorem pairW_unif {TF TJ T3 : Type} (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) :
    (pairW C K D tF tJ t3).Unif :=
  pair3_unif _ _ _ (pairT_unif C K D.ds₁) (pairT_unif C K D.ds₂) (pairT_unif C K D.ds₃)

/-- The link, with its round in front. -/
theorem pairL_unif (ds : List RD) : (pairL C K ds).Unif :=
  Pair.cons_unif (s0 C).up (pairZ_unif C K (z0 ds))

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.Pair.map_oldR_unif
#print axioms AtPublicFiles.Climb.Pair.prRho_old
#print axioms AtPublicFiles.Climb.Honest.prRho_withheld_up
#print axioms AtPublicFiles.Climb.Pair.prRho_zeroR
#print axioms AtPublicFiles.Climb.Pair.prRho_zeroR_le
#print axioms AtPublicFiles.Climb.Honest.prRho_withheld_dn_le
#print axioms AtPublicFiles.Climb.Pair.cons_unif
#print axioms AtPublicFiles.Climb.Pair.app_unif
#print axioms AtPublicFiles.Climb.pair3_unif
#print axioms AtPublicFiles.Climb.rpZ_unif
#print axioms AtPublicFiles.Climb.pairZ_unif
#print axioms AtPublicFiles.Climb.pairT_unif
#print axioms AtPublicFiles.Climb.pairW_unif
#print axioms AtPublicFiles.Climb.pairL_unif
