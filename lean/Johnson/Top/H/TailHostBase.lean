-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailHostBase.lean: the seam from the sending of the reads into the draw of the matrix
of a smallness test, where the joint in front of the sending says that there are integer cells
behind the committed symbols, and the draw's input relation is what makes that true.

Johnson/Top/H/TailHost.lean has the form in which the whole base joint in front of the sending rides
through the smallness test. In a link that joint has two parts: `Cb.Pv.Tail.Base` of the symbols
(Cb/Pv/Tail/Base.lean): there are small integers whose packing the symbols are; and a share Br of
the frame's own. Only Br rides. `Base` comes back from the draw's input relation "there are cells"
(`base_of_relIn`). Statements and proofs.

Main names:
  `tailHost_hrel_base`: the seam's premise at A₀ := `Cb.Sub.virtJ B' a msg₁ n`, the frame's letters
    at B₀ := Br, for every base joint B' whose relaxed relation follows from `Base` of the symbols
    and Br's (`hB`). At B' := "`Base` of the symbols, and Br" (`baseAnd sym Br`,
    Cb/Pv/Tail/InSubOf.lean) `hB` is the pair of its two arguments.
  `tailHostBase_into_ok`, `tailHostBase_cf_ok`: so the seam holds, behind `kSendInto` and behind
    `kSend`.

Limits: those of Johnson/Top/H/TailHost.lean: `Size.Uniq` and the three laws on the frame's letters
are hypotheses. Cb/Pv/Tail/InSubOf.lean is not imported here: `baseAnd` is named in words alone.
-/
import Johnson.Top.H.TailHost
import Cb.Pv.Tail.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles Cb.Sub Cb.Pv.Tail

section
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {s : Size} {K Xe Wp Wp₁ : Type} {Ex : ExtSpec}
  (S₁ : Sig Cb.Gl.E) (snd : Cb.Pv.Send.Size Cb.Gl.E) (bk₁ : snd.N.Msg → Wp₁ → Wp)
  (Br B' : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → Cb.Gl.E)
  (ent : snd.N.Msg → J₂ → Cb.Gl.E)
  (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E)
  (sym : S₁.Msg → Syms Cb.Gl.E s)
  (tab : snd.N.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E)
  (dig : Wp₁ → Dig Cb.Gl.E s)

local notation "Qh" => tailHost S₁ snd bk₁ Br msg₁ ent w sym tab dig
local notation "Dh" => tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig

/-- The seam's premise: Br rides; `Base` is made by the draw's input relation. -/
theorem tailHost_hrel_base (hB : ∀ b v, Base (sym v.1) → Br.relR b v → B'.relR b v) (p : ℕ)
    [CharP Cb.Gl.E p] (hu : s.Uniq p) (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁)
    (it : J₂ → JTab s) (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    ∀ b v, (virtJ B' a msg₁ n).on b → (Cb.Pv.Tail.A (Dh).caller.letters).relR b v →
      (S₁.grow snd.N (virtJ B' a msg₁ n) bk₁).relR b v := by
  intro b v _ h
  obtain ⟨h1, h2, h3⟩ := host_seam (Qh) p hu a ic it hc ha ht
    (fun z => Br.core (S₁.left snd.N (T := OMsg.Msg) z.1,
      bk₁ (S₁.right snd.N (T := OMsg.Msg) z.1) z.2)) b v.1 v.2 h
  exact ⟨hB _ _ (base_of_relIn (Qh).let p hu h.2) h1, (late_holds _ _ _ _ h2).1 h3⟩

/-- The seam behind a sending that ends at a joint with its condition. -/
theorem tailHostBase_into_ok (hB : ∀ b v, Base (sym v.1) → Br.relR b v → B'.relR b v) (p : ℕ)
    [CharP Cb.Gl.E p] (hu : s.Uniq p) (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁)
    (it : J₂ → JTab s) (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    (tailIntoRng (Dh) (virtJ B' a msg₁ n) bk₁).OK :=
  tailIntoRng_ok _ _ _
    (tailHost_hrel_base S₁ snd bk₁ Br B' msg₁ ent w sym tab dig hB p hu a ic it hc ha ht n)

/-- The seam behind a sending that ends at a joint whose condition may fail. -/
theorem tailHostBase_cf_ok (hB : ∀ b v, Base (sym v.1) → Br.relR b v → B'.relR b v) (p : ℕ)
    [CharP Cb.Gl.E p] (hu : s.Uniq p) (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁)
    (it : J₂ → JTab s) (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    (seamToRng (Dh) (virtJ B' a msg₁ n) bk₁).OK :=
  seamToRng_ok _ _ _
    (tailHost_hrel_base S₁ snd bk₁ Br B' msg₁ ent w sym tab dig hB p hu a ic it hc ha ht n)

end

end KObj

#print axioms KObj.tailHost_hrel_base
#print axioms KObj.tailHostBase_into_ok
#print axioms KObj.tailHostBase_cf_ok
