/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.Sorry
/-!
# Coplanar Double Pendulum
### Tag: LnL_1.5.1
## Source:
* Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
* Chapter: 1 The Equations of motion
* Section: 5 The Lagrangian for a system of particles
* Problem: 1 Coplanar Double Pendulum

Description: This problem involves:
a) identifying the appropriate Degrees of Freedom or generalized coordinates
and their relation to cartesian coordinates

b) and using them to write down the Lagrangian for

a coplanar double pendulum made up of two
point masses $m_1$ and $m_2$. Mass $m_1$ is attached to the pivot and $m_2$ is attached
to $m_1$ via strings of length $l_1$ and $l_2$ respectively.

Solution:

The Cartesian coordinates $(x_1, y_1)$ for mass $m_1$ and $(x_2, y_2)$ for mass $m_2$ can be
expressed in terms of the two angles $\phi_1$ and $\phi_2$ made by the strings with the vertical:
$$
\begin{aligned}
x_1 &= l_1\sin\phi_1\\
y_1 &= -l_1\cos\phi_1\\
x_2 &= l_1\sin\phi_1 + l_2\sin\phi_2\\
y_2 &= -l_1\cos\phi_1 - l_2\cos\phi_2
\end{aligned}
$$

b) The Lagrangian is obtained by writing down the kinetic and potential energies
first in terms of cartesian coordinates and their time derivates and then substituting
the coordinates and derivatives with transformations obtained in a) :

$$\mathcal{L} = T_1 + T_2 - V_1 - V_2$$ where $T$ denotes the kinetic energy and $V$
the potential energy
$$
\begin{aligned}
T_1 &= \tfrac{1}{2}m_1(\dot{x}_1^2 + \dot{y}_1^2) = \tfrac{1}{2}m_1 l_1^2\dot{\phi}_1^2\\
V_1 &= m_1 g y_1 = -m_1 g l_1\cos\phi_1\\
T_2 &= \tfrac{1}{2}m_2(\dot{x}_2^2 + \dot{y}_2^2)
    = \tfrac{1}{2}m_2\bigl(l_1^2\dot{\phi}_1^2 + l_2^2\dot{\phi}_2^2
      + 2l_1 l_2\dot{\phi}_1\dot{\phi}_2\cos(\phi_1 - \phi_2)\bigr)\\
V_2 &= m_2 g y_2 = -m_2 g\bigl(l_1\cos\phi_1 + l_2\cos\phi_2\bigr)
\end{aligned}
$$

so that the Lagrangian becomes:
    $$
\mathcal{L} = \tfrac{1}{2}(m_1 + m_2)l_1^2\dot{\phi}_1^2 + \tfrac{1}{2}m_2 l_2^2\dot{\phi}_2^2+
  m_2 l_1 l_2\dot{\phi}_1\dot{\phi}_2\cos(\phi_1 - \phi_2)+
  (m_1 + m_2)g l_1\cos\phi_1 + m_2 g l_2\cos\phi_2
$$
-/

namespace ClassicalMechanics

namespace CoplanarDoublePendulum

/-- The configuration space of the coplaner double pendulum. -/
@[sorryful]
def ConfigurationSpace : Type := sorry

end CoplanarDoublePendulum
end ClassicalMechanics
