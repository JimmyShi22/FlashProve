-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/PackProofs.lean: the proofs of the statements of Iop/Pack.lean, and the point structure of a
packed round.

  `doomed_pack`: `Doomed` (Iop/Rbr.lean) names messages and challenges alone: it goes over to the
    packed list of rounds with the same errors.
  `pack_sound`, `pack_read`, `pack_local`: the three statements.
  `Round.IsPoint.pack`, `Shape.IsPoint.pack`: a packed round's oracle is a string given by its
    columns,
    if an old symbol is the entry of its column (`Packing.OK`) and a column is exactly the tuple of
    its entries (`Packing.Exact`); the finite set of columns is an argument.

-/
import Iop.Pack

namespace Iop
open Prob

theorem rho_unpack : ∀ {s : Shape} (k : Packings s) (τ : Tr (s.pack k)),
    (Tr.unpack k τ).rho = Rho.unpack k τ.rho
  | [], _, _ => rfl
  | _ :: _, (_, ks), (_, c, τ) => congrArg (Prod.mk c) (rho_unpack ks τ)

theorem plains_unpack : ∀ {s : Shape} (k : Packings s) (τ : Tr (s.pack k)),
    (Tr.unpack k τ).plains = Plains.unpack k τ.plains
  | [], _, _ => rfl
  | _ :: _, (_, ks), (m, _, τ) => congrArg (Prod.mk m.2) (plains_unpack ks τ)

theorem doomed_pack : ∀ (s : Shape) (k : Packings s) (ε : Err s) (bad : Tr s → Prop),
    Doomed s ε bad → Doomed (s.pack k) (Err.pack k ε) (fun τ => bad (Tr.unpack k τ))
  | [], _, _, _, h => h
  | _ :: s, (_, ks), (_, ε), bad, h => fun m =>
      le_trans (cnt_mono (fun c hc hd =>
        hc (doomed_pack s ks ε (fun τ => bad (m, c, τ)) hd))) (h m)

theorem pack_sound : Spec.pack_sound := fun _ _ Q k _ ε h x y hn =>
  doomed_pack Q.shape k ε _ (h x y hn)

theorem pack_read : Spec.pack_read := by
  intro s
  induction s with
  | nil => intro _ _ _ p; exact p.elim
  | cons r s ih =>
    rintro ⟨k, ks⟩ ⟨hk, hks⟩ ⟨m, c, τ⟩ p
    cases p with
    | inl p => exact (hk.prj_col m.1 p).symm
    | inr p => exact ih ks hks τ p

theorem pack_local : Spec.pack_local := by
  intro X E Q k hk hQ x y y' τ τ' hρ hpl hext hrd
  letI : DecidableEq (OPos (Q.pack k).shape) := k.dec
  refine hQ x y y' (Tr.unpack k τ) (Tr.unpack k τ') ?_ ?_ ?_ ?_
  · rw [rho_unpack, rho_unpack]; exact congrArg _ hρ
  · rw [plains_unpack, plains_unpack]; exact congrArg _ hpl
  · intro p hp
    rw [rho_unpack] at hp
    exact hext p hp
  · intro p hp
    rw [rho_unpack, plains_unpack] at hp
    rw [pack_read Q.shape k hk τ p, pack_read Q.shape k hk τ' p]
    exact congrArg _ (hrd _ (Finset.mem_image_of_mem _ hp))

/-- The point structure of a packed round. -/
def Round.IsPoint.pack {r : Round} (pt : r.IsPoint) (k : Packing r) (fin : Fintype k.Pos)
    (h : k.OK) (hx : k.Exact) : (r.pack k).IsPoint where
  finPos := fin
  decPos := k.dec
  ofSyms := fun g => pt.ofSyms fun p => k.prj p (g (k.colOf p))
  rd_ofSyms := fun g q => congrFun (hx.ext
    (k.col (pt.ofSyms fun p => k.prj p (g (k.colOf p)))) g fun p => by
      rw [h.prj_col, pt.rd_ofSyms]) q
  ofSyms_rd := fun o => by
    show pt.ofSyms (fun p => k.prj p (k.col o (k.colOf p))) = o
    rw [show (fun p => k.prj p (k.col o (k.colOf p))) = r.rd o from funext (h.prj_col o)]
    exact pt.ofSyms_rd o
  zero := fun q => k.col (pt.ofSyms pt.zero) q

/-- what the point structures of all rounds ask of the datum -/
def Packings.Pt : {s : Shape} → Packings s → Type
  | [], _ => Unit
  | _ :: _, (k, ks) => Fintype k.Pos × Packings.Pt ks

def Packings.Exact : {s : Shape} → Packings s → Prop
  | [], _ => True
  | _ :: _, (k, ks) => k.Exact ∧ Packings.Exact ks

def Shape.IsPoint.pack : {s : Shape} → s.IsPoint → (k : Packings s) → k.Pt → k.OK → k.Exact →
    (s.pack k).IsPoint
  | [], _, _, _, _, _ => ()
  | _ :: _, (pt, pts), (k, ks), (fin, fins), h, hx =>
    (pt.pack k fin h.1 hx.1, Shape.IsPoint.pack pts ks fins h.2 hx.2)

end Iop

#print axioms Iop.pack_sound
#print axioms Iop.pack_local
#print axioms Iop.Round.IsPoint.pack
