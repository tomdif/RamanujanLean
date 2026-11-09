import RamanujanTau.MockTheta5All.All

/-! Axiom audit: the ten fifth-order mock theta identities (`RamanujanTau/MockTheta5All/`).
Each must depend only on `[propext, Classical.choice, Quot.sound]`. -/

-- the ten headline identities
#print axioms MockTheta5All.mock_theta_f0
#print axioms MockTheta5All.mock_theta_f1
#print axioms MockTheta5All.mock_theta_F0
#print axioms MockTheta5All.mock_theta_F1
#print axioms MockTheta5All.mock_theta_phi0
#print axioms MockTheta5All.mock_theta_phi1
#print axioms MockTheta5All.mock_theta_psi0
#print axioms MockTheta5All.mock_theta_psi1
#print axioms MockTheta5All.mock_theta_chi0
#print axioms MockTheta5All.mock_theta_chi1

-- Ramanujan's (B₀), (B₁) and Watson's linear relations
#print axioms MockTheta5All.ramanujan_B0
#print axioms MockTheta5All.ramanujan_B1
#print axioms MockTheta5All.watson_1_0
#print axioms MockTheta5All.watson_1_1
#print axioms MockTheta5All.watson_2_1
#print axioms MockTheta5All.watson_3_1
#print axioms MockTheta5All.euler_odd

-- the seven theta identities
#print axioms MockTheta5All.Theta.theta_phi0
#print axioms MockTheta5All.Theta.theta_F0
#print axioms MockTheta5All.Theta.theta_psi0
#print axioms MockTheta5All.Theta.theta_phi1
#print axioms MockTheta5All.Theta.theta_F1
#print axioms MockTheta5All.Theta.theta_psi1
#print axioms MockTheta5All.Theta.theta_chi1
