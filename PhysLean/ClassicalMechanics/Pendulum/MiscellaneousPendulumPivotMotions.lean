/-
Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlok Vaibhav Singh
-/
/-!
# Miscellaneous Pendulum Pivot Motions
### Tag: LnL_1.5.3
## Source:
* Textbook: Landau and Lifshitz, Mechanics, 3rd Edition
* Chapter 1 The Equations of motion
* Section 5 The Lagrangian for a system of particles
* Problem 3: Pendulum with a moving suspension point

In all three cases described below, the point of support moves in the same plane as the pendulum as
per a given function of time. The lagrangian of the pendulum is to be found.

## Part a)
Description: The pendulum moves uniformally in a vertical circle of radius $a$ and angular velocity
$\gamma$

Solution:
The coordinates of m can be expressed as:
$$
\begin{aligned}
x &= a\cos(\gamma t) + l\sin\phi\\
y &= a\sin(\gamma t) - l\cos\phi
\end{aligned}
$$
(where generalized coordinate, $\phi$, is the angle the string makes
with vertical, $\gamma$ is angle with horizontal)

$$\mathcal{L} = T-V$$ where
Kinetic and potential energies:
$$
\begin{aligned}
T &= \tfrac{1}{2}m(\dot{x}^2 + \dot{y}^2)
= \tfrac{1}{2}m\bigl(l^2\dot{\phi}^2 + 2al\gamma\sin(\phi-\gamma t)\dot{\phi} + a^2\gamma^2\bigr)\\
V &= mg y = mg\bigl(a\sin(\gamma t) - l\cos\phi\bigr)
\end{aligned}
$$

We can ignore the constant term $\tfrac{1}{2}ma^2\gamma^2$ in $T$ as it does not affect the
equations of motion.
Like wise, $mg a\sin(\gamma t)$ in $V$ can be ignored since its contribution to action is constant
Let us note that the total derivative of $a l \cos(\phi - \gamma t)$ is:
$$
\frac{d}{dt}\bigl[al\cos(\phi-\gamma t)\bigr]
= -al\sin(\phi-\gamma t)\dot{\phi} + al\gamma\sin(\phi-\gamma t)
$$

Rearraging the terms, the lagrangian can be written as:
$$
L = \tfrac{1}{2}m l^{2}\dot{\phi}^{2} + m a l \gamma^{2}\sin(\phi-\gamma t) + m g l \cos\phi-
  m\gamma\frac{d}{dt}\bigl[al\cos(\phi-\gamma t)\bigr]
$$
Since lagrangians differing by a total time derivate lead to the same equations of motion
we can ignore the last term. So that the final lagrangian becomes:
$$
L = \tfrac{1}{2}m l^2\dot{\phi}^2 + m a l \gamma^2 \sin(\phi-\gamma t) + m g l \cos\phi
$$

## Part b)
Description: The point of support oscillates horizontally according to the law $x = a\cos(\gamma t)$

Solution:
The coordinates of $m$ can be expressed as:
$$
\begin{aligned}
x &= a\cos(\gamma t) + l\sin\phi\\
y &= -l\cos\phi
\end{aligned}
$$
(where generalized coordinate, $\phi$, is the angle the string makes with vertical)
so that $\dot{x} = -a\gamma\sin(\gamma t) + l\dot{\phi}\cos\phi$ and $\dot{y} = l\dot{\phi}\sin\phi$
$\mathcal{L} = T - V$ where

$$
\begin{aligned}
T &= \tfrac{1}{2}m(\dot{x}^2 + \dot{y}^2)
  = \tfrac{1}{2}m\bigl(l^2\dot{\phi}^2 + a^2\gamma^2\sin^2(\gamma t)
    - 2 a l \gamma\sin(\gamma t)\dot{\phi}\cos\phi\bigr)\\
V &= m g y = - m g l \cos\phi
\end{aligned}
$$
We can ignore the constant term $\tfrac{1}{2}m a^2\gamma^2\sin^2(\gamma t)$ in $T$ again.
The derivative of $\sin\phi\sin(\gamma t)$ is
$$
\frac{d}{dt}\bigl[\sin\phi\sin(\gamma t)\bigr]
= \dot{\phi}\cos\phi\sin(\gamma t) + \gamma\sin\phi\cos(\gamma t)
$$
substituting this in the lagrangian, we get:
$$
L = \tfrac{1}{2} m l^2\dot{\phi}^2 + m a l \gamma^2 \sin\phi\cos(\gamma t) + m g l \cos\phi-
  m a l \gamma\frac{d}{dt}\bigl[\sin\phi\sin(\gamma t)\bigr]
$$

Ignoring the total time derivate term, the final lagrangian becomes:
$$
L = \tfrac{1}{2} m l^2\dot{\phi}^2 + m a l \gamma^2 \sin\phi\cos(\gamma t) + m g l \cos\phi
$$
## Part c)
Description: The point of support oscillates vertically according to the law $y = a\cos(\gamma t)$

Solution:
The coordinates of m can be expressed as:
$$
\begin{aligned}
x &= l\sin\phi\\
y &= a\cos(\gamma t) - l\cos\phi
\end{aligned}
$$
(where generalized coordinate, $\phi$, is angle string makes with vertical)
$L = T - V$ where
$$
\begin{aligned}
T &= \tfrac{1}{2}m(\dot{x}^2 + \dot{y}^2)
  = \tfrac{1}{2}m\bigl(l^2\dot{\phi}^2 + a^2\gamma^2\sin^2(\gamma t)
    - 2 a l \gamma\sin(\gamma t)\dot{\phi}\sin\phi\bigr)\\
V &= m g y = m g\bigl(a\cos(\gamma t) - l\cos\phi\bigr)
\end{aligned}
$$

We can ignore the constant term $\tfrac{1}{2}m a^2\gamma^2\sin^2(\gamma t)$ in $T$ as it does not
lead to variation.
Likewise, $m g a\cos(\gamma t)$ in $V$ can be ignored since its contribution to action is constant.
The time derivative of $\cos\phi\sin(\gamma t)$ is:
$$
\frac{d}{dt}\bigl[\cos\phi\sin(\gamma t)\bigr]
= -\dot{\phi}\sin\phi\sin(\gamma t) + \gamma\cos\phi\cos(\gamma t)
$$
substituting this in the lagrangian, we get:
$$
L = \tfrac{1}{2} m l^2\dot{\phi}^2 + m g l \cos\phi -
  m a l \gamma^2 \cos\phi\cos(\gamma t) +
  m a l \gamma\frac{d}{dt}\bigl[\cos\phi\cos(\gamma t)\bigr]
$$
Ignoring the total time derivate term, the final lagrangian becomes:
$$
L = \tfrac{1}{2} m l^2\dot{\phi}^2 + m g l \cos\phi - m a l \gamma^2 \cos\phi\cos(\gamma t)
$$
-/

namespace ClassicalMechanics

end ClassicalMechanics
