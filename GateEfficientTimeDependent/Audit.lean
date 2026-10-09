import GateEfficientTimeDependent.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 2 lemmas about slot indices,
whose reports list a subset of these three axioms. The audits cover every
theorem of the library, beginning with the final theorem. -/

/-! ### Final theorem, error against every propagator, mesh and sparse parameters -/

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.simCircuitT_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.simCircuitT_public

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.two_pow_clog_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.two_pow_clog_lt

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.meshExp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.meshExp_spec

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.propagator_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.propagator_error

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.sparse_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.sparse_counts

/-! ### Slot-selected semantics, reuse step, selection and agreement -/

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.slotOracle_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.slotOracle_adjoint

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.slotOracle_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.slotOracle_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.pres2_slotOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.pres2_slotOracle

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.slotOracle_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.slotOracle_congr

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.secOracleT_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.secOracleT_emb

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.pres2_secOracleT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.pres2_secOracleT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.secOracleT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.secOracleT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_nil

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_cons

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_append

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_singleton

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.adjT_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.adjT_adjoint

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.evalT_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.evalT_inv

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.adjT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.adjT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.evalT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.evalT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_invList

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_ofGates

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_eq_run

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.evalT_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.evalT_congr

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_congr

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.runT_privI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.runT_privI

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.bnetI_noPriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.bnetI_noPriv

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.STEPT_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.STEPT_emb

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.selectNT_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.selectNT_emb

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.select_blockT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.select_blockT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.pres2_STEPT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.pres2_STEPT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.pres2_selectNT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.pres2_selectNT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.STEPT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.STEPT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.selectNT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.selectNT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.stepT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.stepT_agrees

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.selectT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.selectT_agrees

/-! ### LCU, amplification and the slot-selected simulator -/

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.lcu_blockT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.lcu_blockT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.pres2_LCUT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.pres2_LCUT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.LCUT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.LCUT_isUnitary

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.lcuT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.lcuT_agrees

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.AMPT_io' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.AMPT_io

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.ampT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.ampT_agrees

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.lcu_compressionT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.lcu_compressionT

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.netB_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.netB_slot

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.netG_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.netG_slot

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.cayley_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.cayley_isometry

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.evolution_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.evolution_isometry

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.isometry_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.isometry_norm_le

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.evolution_eq_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.evolution_eq_of_lt

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.exp_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.exp_norm_le_one

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.cayley_evolution_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.cayley_evolution_error

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.releasedV_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.releasedV_bound

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.ampT_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.ampT_error

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.clampAt_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.clampAt_of_lt

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.min_pred_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.min_pred_lt

/-- info: 'SparseHamiltonian.GateCircuit.SlotSim.simulationT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.SlotSim.simulationT
