-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/NoCoinExits.lean: an algorithm without coins (`OComp.NoCoin`, Rom/Cache.lean) stays one under
the changes of oracles: the splitting of answers (Rom/SpecCut.lean), the expansion from a state
under a rule (Rom/StateFirstLazy.lean: a query to an oracle with a long answer is replaced by a
query for a state σ and queries dr (σ, j) to one further oracle dr, one for each hash block that the
rule asks for), the step to one hash function (Rom/Family.lean), and the translation to
ZKCP/Defs.lean (Rom/Bridge.lean).

  `noCoin_cut`, `noCoin_stateFirstA`, `noCoin_overOne`
                        Each step replaces a query by queries and samples nothing.
  `drawsNoCoin_ofRom`   The translated algorithm has `OComp.DrawsNoCoin` of ZKCP/Main.lean.

Besides the helpers `noCoin_askAd`, `noCoin_expandA`, `noCoin_askAll` it proves nothing else.

Notation:
  `c.NoCoin` (Rom/Cache.lean): no path of the algorithm samples coins
  `C o`: in `noCoin_cut` `OCut (S.Rng o)` (Rom/SpecCut.lean), else `Link lam (S.Rng o)`
    (Rom/StateFirst.lean): how an oracle with answers in R is treated; of `Link`: `plain`, or
    `chain K e` with `e : R ≃ (Fin K → Dg lam) × Dg lam × Dg lam`
  `lam`: `ℕ`; `Dg lam`: `Fin lam → Bool` (Rom/NeedA.lean): a hash block
  `askAd C σ nd K j acc` (Rom/StateFirstLazy.lean): the queries to dr at a state under a rule: K
    indices from j on; acc: the hash blocks so far
  `expandA C c nd a` (Rom/StateFirstLazy.lean): from the answer of the second family (`stSpec`) to
    the typed answer, under a rule
  `acc0 lam` (Rom/NeedA.lean): no hash block yet: the all-zero sequence
-/
import Rom.Cache
import Rom.SpecCut
import Rom.StateFirstLazy
import Rom.Family
import Rom.Bridge
import ZKCP.Main

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {α β : Type}

theorem noCoin_cut (C : ∀ o, OCut (S.Rng o)) (need : NeedCut C) :
    ∀ c : OComp S α, c.NoCoin → (c.cut C need).NoCoin
  | .pure _, _ => trivial
  | .query o q k, h => fun a => by
      show (if (C o).isWhole || !need o q a then (k ((C o).alone a)).cut C need
        else
          .query (S := cutSpec S C) (.inr o) q fun b =>
            (k ((C o).join a b)).cut C need : OComp (cutSpec S C) α).NoCoin
      split
      · exact noCoin_cut C need _ (h _)
      · exact fun b => noCoin_cut C need _ (h _)
  | .sample _ _, h => h.elim

variable {lam : ℕ}

theorem noCoin_askAd (C : ∀ o, Link lam (S.Rng o))
    (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), (askAd C σ nd K j acc).NoCoin
  | 0, _, _ => trivial
  | K + 1, j, acc => by
      unfold askAd
      split
      · exact fun r => noCoin_askAd C σ nd K (j + 1) _
      · exact noCoin_askAd C σ nd K (j + 1) acc

theorem noCoin_expandA (C : ∀ o, Link lam (S.Rng o)) {R : Type} :
    ∀ (c : Link lam R) (nd : ℕ → (ℕ → Dg lam) → Bool) (a : c.Ans), (expandA C c nd a).NoCoin
  | .plain, _, _ => trivial
  | .chain K e, nd, σ => by
      show ((askAd C σ nd K 0 (acc0 lam)).bind fun acc =>
        .pure (e.symm ((fun i : Fin K => acc i.val), σ))).NoCoin
      exact OComp.NoCoin.bind (noCoin_askAd C σ nd K 0 _) fun _ => trivial

theorem noCoin_stateFirstA (C : ∀ o, Link lam (S.Rng o)) (need : NeedA S lam) :
    ∀ c : OComp S α, c.NoCoin → (c.stateFirstA C need).NoCoin
  | .pure _, _ => trivial
  | .query o q k, h =>
    fun a =>
      OComp.NoCoin.bind (noCoin_expandA C (C o) (need o q) a) fun r =>
        noCoin_stateFirstA C need (k r) (h r)
  | .sample _ _, h => h.elim

theorem noCoin_askAll : ∀ (n : ℕ) (g : Fin n → List Bool), (askAll lam n g).NoCoin
  | 0, _ => trivial
  | n + 1, g => fun _ => OComp.NoCoin.bind (noCoin_askAll n fun i => g i.succ) fun _ => trivial

theorem noCoin_overOne (m : OracleCoding S lam) : ∀ c : OComp S α, c.NoCoin → (c.overOne m).NoCoin
  | .pure _, _ => trivial
  | .query _ _ k, h => OComp.NoCoin.bind (noCoin_askAll _ _) fun _ => noCoin_overOne m (k _) (h _)
  | .sample _ _, h => h.elim

theorem drawsNoCoin_ofRom : ∀ c : OComp (rom lam) α, c.NoCoin → (ofRom c).DrawsNoCoin
  | .pure _, _ => trivial
  | .query _ _ k, h => fun r => drawsNoCoin_ofRom (k r) (h r)
  | .sample _ _, h => h.elim

end Rom
