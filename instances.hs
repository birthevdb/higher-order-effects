%==================================================================
\section{Instances of the Generic Monad}
\label{sec:instances}

Different effects (algebraic and higher-order) can be viewed as instances
of our generic framework, defining an appropriate higher-order functor that maps their
signature to the generic setting.
%
In particular, \emph{instantiating the framework} consists of four steps:

% \setlist[itemize]{leftmargin=15mm}
\begin{itemize}
  \item[\textbf{(1)}] Map the effect signatures to a higher-order representation
  by defining a higher-order functor |K| that maps a functor |F| and type |A| onto a type
  of kind |*|.
% < K F A = ...
  \item[\textbf{(2)}] Show that this |K| is indeed a higher-order functor.
% < instance HOFunctor K where ...
  \item[\textbf{(3)}] Plug it in the generic free monad |T| and show that it is isomorphic to the
  specialized effect definition.
% < T K a iso ...
  \item[\textbf{(4)}] Use the generic |fold| function to write a handler for the effects and show
  that it is isomorphic to the specialized effect handler (if it exists).
\end{itemize}

In what follows, we instantiate our framework using these four steps for different classes
of effects.