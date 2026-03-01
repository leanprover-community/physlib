/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
import PhysLean.Meta.Sorry
/-!
# Sliding Pendulum
### Tag: LnL_1.5.2
## Source:
* Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
* Chapter: 1 The Equations of motion
* Section: 5 The Lagrangian for a system of particles
* Problem: 2 Sliding Pendulum

Description:
A simple pendulum of mass $m_2$ attached to a mass $m_1$ as its point of support via a string of
length $l$. The mass $m_1$ is free to move horizontally.
The Lagrangian of the system is to be found.

Solution:
First, the constraints are identified:
$$
\begin{aligned}
y_1 &= 0\\
(x_2 - x_1)^2 + (y_2 - y_1)^2 &= l^2
\end{aligned}
$$
And the second constraint gives:
$$
\begin{aligned}
x_2 - x_1 &= l\sin\phi\\
y_2 - y_1 &= y_2 = -\,l\cos\phi
\end{aligned}
$$
with the generalized coordinate $\phi$ being the angle the string makes with the vertical.

The Lagrangian is obtained as:
$$\mathcal{L} = T_1 + T_2 - V_1 - V_2$$ where

$$
\begin{aligned}
T_1 &= \tfrac{1}{2} m_1 \dot{x}_1^2, & V_1 &= 0,\\[4pt]
T_2 &= \tfrac{1}{2} m_2(\dot{x}_2^2 + \dot{y}_2^2)
    = \tfrac{1}{2} m_2\bigl(l^2\dot{\phi}^2 + \dot{x}_1^2 + 2l\dot{\phi}\dot{x}_1\cos\phi\bigr),
    & V_2 &= m_2 g y_2 = -m_2 g l \cos\phi
\end{aligned}
$$

Thus the Lagrangian is
$$
\mathcal{L} = \tfrac{1}{2}(m_1 + m_2)\dot{x}_1^2 + \tfrac{1}{2} m_2\bigl(l^2\dot{\phi}^2+
2l\dot{\phi}\dot{x}_1\cos\phi\bigr) + m_2 g l \cos\phi
$$

-/

namespace ClassicalMechanics

namespace SlidingPendulum

/-- The configuration space of the sliding pendulum system. -/
@[sorryful]
def ConfigurationSpace : Type := sorry

end SlidingPendulum

end ClassicalMechanics
