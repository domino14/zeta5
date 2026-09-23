pts=[tuple(map(int,l.split())) for l in open('gen/pts62.txt')]
def q(p): return f"({p[0]} / {p[1]} : ℚ)" if p[1]!=1 else f"({p[0]} : ℚ)"
N=100
chunks=[pts[i:i+N] for i in range(0,len(pts),N)]
starts=[(0,1)]+[c[-1] for c in chunks[:-1]]
out=["""import Zeta5.Lemma61Pot

/-!
# Lemma 6.1, (6.2): the kernel-checked partition of `[0, 2]`

The partition was produced by a greedy search with the checker `Pot.chk` itself
(`gen/gen_check62.py`, points in `gen/pts62.txt`); every interval is re-checked here by
`decide +kernel`.
-/

open Finset MeasureTheory Set

namespace Zeta5

namespace Pot
"""]
for i,c in enumerate(chunks):
    out.append(f"def C{i} : List ℚ := [{', '.join(q(p) for p in c)}]\n")
for i,c in enumerate(chunks):
    out.append(f"""set_option maxRecDepth 100000 in
theorem chain_C{i} : chain {q(starts[i])} C{i} = true := by decide +kernel
""")
    out.append(f"""theorem lastD_C{i} : lastD {q(starts[i])} C{i} = {q(c[-1])} := by decide +kernel
""")
n=len(chunks)
allp=" ++ (".join(f"C{i}" for i in range(n))+")"*(n-1)
out.append(f"def allPts : List ℚ := {allp}\n")
out.append("""lemma chain_join (l m : ℚ) (xs ys : List ℚ) (h1 : chain l xs = true) (hm : lastD l xs = m)
    (h2 : chain m ys = true) : chain l (xs ++ ys) = true := by
  rw [chain_append, h1, hm, h2]; rfl
""")
# build nested proof from the end
expr=f"chain_C{n-1}"
for i in range(n-2,-1,-1):
    expr=f"chain_join _ _ _ _ chain_C{i} lastD_C{i} ({expr})"
out.append(f"theorem chain_all : chain 0 allPts = true :=\n  {expr}\n")
lastexpr=" ".join(f"lastD_append," for _ in range(n-1))
out.append(f"""theorem lastD_all : lastD 0 allPts = 2 := by
  unfold allPts
  simp only [lastD_append, lastD_C0, {', '.join(f'lastD_C{i}' for i in range(1,n))}]
""")
out.append("""theorem bound_0_2 (t : ℝ) (h0 : 0 ≤ t) (h2 : t ≤ 2) : 2 * logPot rho t - V t ≤ Bd :=
  chain_sound allPts 0 chain_all (by simp [allPts, C0]) t (by simpa using h0)
    (by rw [lastD_all]; simpa using h2)

end Pot

/-- (A.9) with (6.8): `2U^ρ(t) - V(t) < -6645002/10⁶` for `t ≥ 0`. -/
theorem potential_A9' (t : ℝ) (ht : 0 ≤ t) : 2 * logPot rho t - V t < -6645002 / 10 ^ 6 := by
  rcases le_or_gt t 2 with h | h
  · have := Pot.bound_0_2 t ht h
    have hB : ((Pot.Bd : ℚ) : ℝ) < -6645002 / 10 ^ 6 := by unfold Pot.Bd; push_cast; norm_num
    linarith
  · exact Pot.tail_bound t h.le

/-- Lemma 6.1. -/
theorem lemma_6_1' :
    rho Set.univ = ENNReal.ofReal (Lim.lam) ∧ rho (Set.Ioo 0 2)ᶜ = 0 ∧
      (∀ t : ℝ, 0 ≤ t → 2 * logPot rho t - V t ≤ M0) ∧
      (Lim.lam * M0 - logEnergy rho + Cstar ≤ U) := by
  refine ⟨rho_univ, rho_compl, fun t ht => ?_, energy_6_4⟩
  have := potential_A9' t ht
  have hM : (-6645002 / 10 ^ 6 : ℝ) ≤ (M0 : ℝ) := by unfold M0; push_cast; norm_num
  linarith

end Zeta5
""")
open('Zeta5/Zeta5/Lemma61Check.lean','w').write("\n".join(out))
print(len(chunks))
