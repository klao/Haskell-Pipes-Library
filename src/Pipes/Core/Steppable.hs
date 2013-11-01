{-| The core functionality for the 'ProxySteppable' monad transformer

    Read "Pipes.Tutorial" if you want a beginners tutorial explaining how to use
    this library.  The documentation in this module targets more advanced users
    who want to understand the theory behind this library.

    This module is not exported by default, and I recommend you use the
    unidirectional operations exported by the "Pipes" module if you can.  You
    should only use this module if you require advanced features like:

    * bidirectional communication, or:

    * push-based 'Pipe's.
-}

{-# LANGUAGE CPP, RankNTypes #-}

#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{- The rewrite RULES require the 'TrustWorthy' annotation.  Their proofs are
   pretty trivial since they are just inlining the definition of their
   respective operators.  GHC doesn't do this inlining automatically for these
   functions because they are recursive.
-}

-- TODO(klao): most of these are probably unnecessary.

module Pipes.Core.Steppable (
    -- * ProxySteppable Monad Transformer
    -- $proxy
    ProxySteppable,
    runEffectSteppable,

    -- * Categories
    -- $categories

    -- ** Respond
    -- $respond
    respondSteppable,
    (/>/.),
    (//>.),

    -- ** Request
    -- $request
    requestSteppable,
    (\>\.),
    (>\\.),

    -- ** Push
    -- $push
    pushSteppable,
    (>~>.),
    (>>~.),

    -- ** Pull
    -- $pull
    pullSteppable,
    (>+>.),
    (+>>.),

    -- ** Reflect
    -- $reflect
    reflectSteppable,

    -- * Concrete Type Synonyms
    EffectSteppable,
    ProducerSteppable,
    PipeSteppable,
    ConsumerSteppable,
    ClientSteppable,
    ServerSteppable,

    -- * Polymorphic Type Synonyms
    EffectSteppable',
    ProducerSteppable',
    ConsumerSteppable',
    ClientSteppable',
    ServerSteppable',

    -- * Flipped operators
    (\<\.),
    (/</.),
    (<~<.),
    (~<<.),
    (<+<.),
    (<\\.),
    (//<.),
    (<<+.)
    ) where

import Data.Void (Void, absurd)
import Pipes.Internal (ProxySteppable(..))

{- $proxy
    Diagrammatically, you can think of a 'ProxySteppable' as having the following shape:

@
 Upstream | Downstream
     +---------+
     |         |
 a' <==       <== b'
     |         |
 a  ==>       ==> b
     |    |    |
     +----|----+
          v
          r
@

    You can connect proxies together in five different ways:

    * ('Pipes.>+>.'): connect pull-based streams

    * ('Pipes.>~>.'): connect push-based streams

    * ('Pipes.\>\.'): chain folds

    * ('Pipes./>/.'): chain unfolds

    * ('Control.Monad.>=>'): sequence proxies

-}

-- | Run a self-contained 'EffectSteppable', converting it back to the base monad
runEffectSteppable :: (Monad m) => EffectSteppable m r -> m r
runEffectSteppable = go
  where
    go p = case p of
        Request v _ -> absurd v
        Respond v _ -> absurd v
        M       m   -> m >>= go
        Pure    r   -> return r
{-# INLINABLE runEffectSteppable #-}

{-
   * Keep proxy composition lower in precedence than function composition, which
     is 9 at the time of of this comment, so that users can write things like:


> lift . k >+>. p
>
> hoist f . k >+>. p

   * Keep the priorities different so that users can mix composition operators
     like:

> up \>\. p />/. dn
>
> up >~>. p >+>. dn

   * Keep 'requestSteppable' and 'respondSteppable' composition lower in precedence than 'pull'
     and 'pushSteppable' composition, so that users can do:

> read \>\. pullSteppable >+>. writer

   * I arbitrarily choose a lower priority for downstream operators so that lazy
     pull-based computations need not evaluate upstream stages unless absolutely
     necessary.
-}
infixl 3 //>.
infixr 3 <\\.
infixr 4 />/., >\\.
infixl 4 \<\., //<.
infixl 5 \>\.
infixr 5 /</.
infixl 6 <<+.
infixr 6 +>>.
infixl 7 >+>., >>~.
infixr 7 <+<., ~<<.
infixl 8 <~<.
infixr 8 >~>.

{- $categories
    A 'Control.Category.Category' is a set of components that you can connect
    with a composition operator, ('Control.Category..'), that has an identity,
    'Control.Category.id'.  The ('Control.Category..') and 'Control.Category.id'
    must satisfy the following three 'Control.Category.Category' laws:

@
\-\- Left identity
'Control.Category.id' 'Control.Category..' f = f

\-\- Right identity
f 'Control.Category..' 'Control.Category.id' = f

\-\- Associativity
(f 'Control.Category..' g) 'Control.Category..' h = f 'Control.Category..' (g 'Control.Category..' h)
@

    The 'ProxySteppable' type sits at the intersection of five separate categories, four
    of which are named after their identity:

@
                     Identity   | Composition |  Point-ful
                  +-------------+-------------+-------------+
 respond category |   'respondSteppable'   |     '/>/.'     |     '//>.'     |
 request category |   'requestSteppable'   |     '\>\.'     |     '>\\.'     |
    push category |   'pushSteppable'      |     '>~>.'     |     '>>~.'     |
    pull category |   'pullSteppable'      |     '>+>.'     |     '+>>.'     |
 Kleisli category |   'return'    |     'Control.Monad.>=>'     |     '>>='     |
                  +-------------+-------------+-------------+
@

    Each composition operator has a \"point-ful\" version, analogous to how
    ('>>=') is the point-ful version of ('Control.Monad.>=>').  For example,
    ('//>.') is the point-ful version of ('/>/.').  The convention is that the
    odd character out faces the argument that is a function.
-}

{- $respondSteppable
    The 'respondSteppable' category closely correspondSteppables to the generator design pattern.

    The 'respondSteppable' category obeys the category laws, where 'respondSteppable' is the
    identity and ('/>/.') is composition:

@
\-\- Left identity
'respondSteppable' '/>/.' f = f

\-\- Right identity
f '/>/.' 'respondSteppable' = f

\-\- Associativity
(f '/>/.' g) '/>/.' h = f '/>/.' (g '/>/.' h)
@

    The following diagrams show the flow of information:

@
'respondSteppable' :: ('Monad' m)
       =>  a -> 'ProxySteppable' x' x a' a m a'

\          a
          |
     +----|----+
     |    |    |
 x' <==   \\ /==== a'
     |     X   |
 x  ==>   / \\===> a
     |    |    |
     +----|----+
          v 
          a'

('/>/.') :: ('Monad' m)
      => (a -> 'ProxySteppable' x' x b' b m a')
      -> (b -> 'ProxySteppable' x' x c' c m b')
      -> (a -> 'ProxySteppable' x' x b' b m a')

\          a                   /===> b                      a
          |                  /      |                      |
     +----|----+            /  +----|----+            +----|----+
     |    v    |           /   |    v    |            |    v    |
 x' <==       <== b' <==\\ / x'<==       <== c'    x' <==       <== c'
     |    f    |         X     |    g    |     =      | f '/>/.' g |
 x  ==>       ==> b  ===/ \\ x ==>       ==> c     x  ==>       ==> c'
     |    |    |           \\   |    |    |            |    |    |
     +----|----+            \\  +----|----+            +----|----+
          v                  \\      v                      v
          a'                  \\==== b'                     a'
@

-}

{-| Send a value of type @a@ downstream and block waiting for a reply of type
    @a'@

    'respondSteppable' is the identity of the respondSteppable category.
-}
respondSteppable :: (Monad m) => a -> ProxySteppable x' x a' a m a'
respondSteppable a = Respond a Pure
{-# INLINABLE respondSteppable #-}

{-| Compose two unfolds, creating a new unfold

@
(f '/>/.' g) x = f x '//>.' g
@

    ('/>/.') is the composition operator of the respondSteppable category.
-}
(/>/.)
    :: (Monad m)
    => (a -> ProxySteppable x' x b' b m a')
    -- ^
    -> (b -> ProxySteppable x' x c' c m b')
    -- ^
    -> (a -> ProxySteppable x' x c' c m a')
    -- ^
(fa />/. fb) a = fa a //>. fb
{-# INLINABLE (/>/.) #-}

{-| @(p \/\/> f)@ replaces each 'respondSteppable' in @p@ with @f@.

    Point-ful version of ('/>/.')
-}
(//>.)
    :: (Monad m)
    =>       ProxySteppable x' x b' b m a'
    -- ^
    -> (b -> ProxySteppable x' x c' c m b')
    -- ^
    ->       ProxySteppable x' x c' c m a'
    -- ^
p0 //>. fb = go p0
  where
    go p = case p of
        Request x' fx  -> Request x' (\x -> go (fx x))
        Respond b  fb' -> fb b >>= \b' -> go (fb' b')
        M          m   -> M (m >>= \p' -> return (go p'))
        Pure       a   -> Pure a
{-# INLINABLE (//>.) #-}

{-# RULES
    "(Request x' fx ) //>. fb" forall x' fx  fb .
        (Request x' fx ) //>. fb = Request x' (\x -> fx x //>. fb);
    "(Respond b  fb') //>. fb" forall b  fb' fb .
        (Respond b  fb') //>. fb = fb b >>= \b' -> fb' b' //>. fb;
    "(M          m  ) //>. fb" forall    m   fb .
        (M          m  ) //>. fb = M (m >>= \p' -> return (p' //>. fb));
    "(Pure      a   ) //>. fb" forall a      fb .
        (Pure    a     ) //>. fb = Pure a;
  #-}

{- $requestSteppable
    The 'requestSteppable' category closely correspondSteppables to the iteratee design pattern.

    The 'requestSteppable' category obeys the category laws, where 'requestSteppable' is the
    identity and ('\>\.') is composition:

@
-- Left identity
'requestSteppable' '\>\.' f = f

\-\- Right identity
f '\>\.' 'requestSteppable' = f

\-\- Associativity
(f '\>\.' g) '\>\.' h = f '\>\.' (g '\>\.' h)
@

    The following diagrams show the flow of information:

@
'requestSteppable' :: ('Monad' m)
        =>  a' -> 'ProxySteppable' a' a y' y m a

\          a'
          |
     +----|----+
     |    |    |
 a' <=====/   <== y'
     |         |
 a  ======\\   ==> y
     |    |    |
     +----|----+
          v
          a

('\>\.') :: ('Monad' m)
      => (b' -> 'ProxySteppable' a' a y' y m b)
      -> (c' -> 'ProxySteppable' b' b y' y m c)
      -> (c' -> 'ProxySteppable' a' a y' y m c)

\          b'<=====\\                c'                     c'
          |        \\               |                      |
     +----|----+    \\         +----|----+            +----|----+
     |    v    |     \\        |    v    |            |    v    |
 a' <==       <== y'  \\== b' <==       <== y'    a' <==       <== y'
     |    f    |              |    g    |     =      | f '\>\.' g |
 a  ==>       ==> y   /=> b  ==>       ==> y     a  ==>       ==> y
     |    |    |     /        |    |    |            |    |    |
     +----|----+    /         +----|----+            +----|----+
          v        /               v                      v
          b ======/                c                      c
@
-}

{-| Send a value of type @a'@ upstream and block waiting for a reply of type @a@

    'requestSteppable' is the identity of the requestSteppable category.
-}
requestSteppable :: (Monad m) => a' -> ProxySteppable a' a y' y m a
requestSteppable a' = Request a' Pure
{-# INLINABLE requestSteppable #-}

{-| Compose two folds, creating a new fold

@
(f '\>\.' g) x = f '>\\.' g x
@

    ('\>\.') is the composition operator of the requestSteppable category.
-}
(\>\.)
    :: (Monad m)
    => (b' -> ProxySteppable a' a y' y m b)
    -- ^
    -> (c' -> ProxySteppable b' b y' y m c)
    -- ^
    -> (c' -> ProxySteppable a' a y' y m c)
    -- ^
(fb' \>\. fc') c' = fb' >\\. fc' c'
{-# INLINABLE (\>\.) #-}

{-| @(f >\\.\\ p)@ replaces each 'requestSteppable' in @p@ with @f@.

    Point-ful version of ('\>\.')
-}
(>\\.)
    :: (Monad m)
    => (b' -> ProxySteppable a' a y' y m b)
    -- ^
    ->        ProxySteppable b' b y' y m c
    -- ^
    ->        ProxySteppable a' a y' y m c
    -- ^
fb' >\\. p0 = go p0
  where
    go p = case p of
        Request b' fb  -> fb' b' >>= \b -> go (fb b)
        Respond x  fx' -> Respond x (\x' -> go (fx' x'))
        M          m   -> M (m >>= \p' -> return (go p'))
        Pure       a   -> Pure a
{-# INLINABLE (>\\.) #-}

{-# RULES
    "fb' >\\. (Request b' fb )" forall fb' b' fb  .
        fb' >\\. (Request b' fb ) = fb' b' >>= \b -> fb' >\\. fb  b;
    "fb' >\\. (Respond x  fx')" forall fb' x  fx' .
        fb' >\\. (Respond x  fx') = Respond x (\x' -> fb' >\\. fx' x');
    "fb' >\\. (M          m  )" forall fb'    m   .
        fb' >\\. (M          m  ) = M (m >>= \p' -> return (fb' >\\. p'));
    "fb' >\\. (Pure    a    )" forall fb' a      .
        fb' >\\. (Pure    a     ) = Pure a;
  #-}

{- $push
    The 'pushSteppable' category closely correspondSteppables to push-based Unix pipes.

    The 'push' category obeys the category laws, where 'pushSteppable' is the identity
    and ('>~>.') is composition:

@
\-\- Left identity
'pushSteppable' '>~>.' f = f

\-\- Right identity
f '>~>.' 'pushSteppable' = f

\-\- Associativity
(f '>~>.' g) '>~>.' h = f '>~>.' (g '>~>.' h)
@

    The following diagram shows the flow of information:

@
'pushSteppable'  :: ('Monad' m)
      =>  a -> 'ProxySteppable' a' a a' a m r

\          a
          |
     +----|----+
     |    v    |
 a' <============ a'
     |         |
 a  ============> a
     |    |    |
     +----|----+
          v
          r

('>~>.') :: ('Monad' m)
      => (a -> 'ProxySteppable' a' a b' b m r)
      -> (b -> 'ProxySteppable' b' b c' c m r)
      -> (a -> 'ProxySteppable' a' a c' c m r)

\          a                b                      a
          |                |                      |
     +----|----+      +----|----+            +----|----+
     |    v    |      |    v    |            |    v    |
 a' <==       <== b' <==       <== c'    a' <==       <== c'
     |    f    |      |    g    |     =      | f '>~>.' g |
 a  ==>       ==> b  ==>       ==> c     a  ==>       ==> c
     |    |    |      |    |    |            |    |    |
     +----|----+      +----|----+            +----|----+
          v                v                      v
          r                r                      r
@

-}

{-| Forward responses followed by requestSteppables

@
'pushSteppable' = 'respondSteppable' 'Control.Monad.>=>' 'requestSteppable' 'Control.Monad.>=>' 'pushSteppable'
@

    'pushSteppable' is the identity of the push category.
-}
pushSteppable :: (Monad m) => a -> ProxySteppable a' a a' a m r
pushSteppable = go
  where
    go a = Respond a (\a' -> Request a' go)
{-# INLINABLE pushSteppable #-}

{-| Compose two proxies blocked while 'requestSteppable'ing data, creating a new proxy
    blocked while 'requestSteppable'ing data

@
(f '>~>.' g) x = f x '>>~.' g
@

    ('>~>.') is the composition operator of the push category.
-}
(>~>.)
    :: (Monad m)
    => (_a -> ProxySteppable a' a b' b m r)
    -- ^
    -> ( b -> ProxySteppable b' b c' c m r)
    -- ^
    -> (_a -> ProxySteppable a' a c' c m r)
    -- ^
(fa >~>. fb) a = fa a >>~. fb
{-# INLINABLE (>~>.) #-}

{-| @(p >>~. f)@ pairs each 'respondSteppable' in @p@ with an 'requestSteppable' in @f@.

    Point-ful version of ('>~>.')
-}
(>>~.)
    :: (Monad m)
    =>       ProxySteppable a' a b' b m r
    -- ^
    -> (b -> ProxySteppable b' b c' c m r)
    -- ^
    ->       ProxySteppable a' a c' c m r
    -- ^
p >>~. fb = case p of
    Request a' fa  -> Request a' (\a -> fa a >>~. fb)
    Respond b  fb' -> fb' +>>. fb b
    M          m   -> M (m >>= \p' -> return (p' >>~. fb))
    Pure       r   -> Pure r
{-# INLINABLE (>>~.) #-}

{- $pull
    The 'pull' category closely correspondSteppables to pull-based Unix pipes.

    The 'pull' category obeys the category laws, where 'pullSteppable' is the identity
    and ('>+>.') is composition:

@
\-\- Left identity
'pullSteppable' '>+>.' f = f

\-\- Right identity
f '>+>.' 'pullSteppable' = f

\-\- Associativity
(f '>+>.' g) '>+>.' h = f '>+>.' (g '>+>.' h)
@

    The following diagrams show the flow of information:

@
'pullSteppable'  :: ('Monad' m)
      =>  a' -> 'ProxySteppable' a' a a' a m r

\          a'
          |
     +----|----+
     |    v    |
 a' <============ a'
     |         |
 a  ============> a
     |    |    |
     +----|----+
          v
          r

('>+>.') :: ('Monad' m)
      -> (b' -> 'ProxySteppable' a' a b' b m r)
      -> (c' -> 'ProxySteppable' b' b c' c m r)
      -> (c' -> 'ProxySteppable' a' a c' c m r)

\          b'               c'                     c'
          |                |                      |
     +----|----+      +----|----+            +----|----+
     |    v    |      |    v    |            |    v    |
 a' <==       <== b' <==       <== c'    a' <==       <== c'
     |    f    |      |    g    |     =      | f >+>. g |
 a  ==>       ==> b  ==>       ==> c     a  ==>       ==> c
     |    |    |      |    |    |            |    |    |
     +----|----+      +----|----+            +----|----+
          v                v                      v
          r                r                      r
@

-}

{-| Forward requestSteppables followed by responses:

@
'pullSteppable' = 'requestSteppable' 'Control.Monad.>=>' 'respondSteppable' 'Control.Monad.>=>' 'pullSteppable'
@

    'pullSteppable' is the identity of the pull category.
-}
pullSteppable :: (Monad m) => a' -> ProxySteppable a' a a' a m r
pullSteppable = go
  where
    go a' = Request a' (\a -> Respond a go)
{-# INLINABLE pullSteppable #-}

{-| Compose two proxies blocked in the middle of 'respondSteppable'ing, creating a new
    proxy blocked in the middle of 'respondSteppable'ing

@
(f '>+>.' g) x = f '+>>.' g x
@

    ('>+>.') is the composition operator of the pull category.
-}
(>+>.)
    :: (Monad m)
    => ( b' -> ProxySteppable a' a b' b m r)
    -- ^
    -> (_c' -> ProxySteppable b' b c' c m r)
    -- ^
    -> (_c' -> ProxySteppable a' a c' c m r)
    -- ^
(fb' >+>. fc') c' = fb' +>>. fc' c'
{-# INLINABLE (>+>.) #-}

{-| @(f +>>. p)@ pairs each 'requestSteppable' in @p@ with a 'respondSteppable' in @f@.

    Point-ful version of ('>+>.')
-}
(+>>.)
    :: (Monad m)
    => (b' -> ProxySteppable a' a b' b m r)
    -- ^
    ->        ProxySteppable b' b c' c m r
    -- ^
    ->        ProxySteppable a' a c' c m r
    -- ^
fb' +>>. p = case p of
    Request b' fb  -> fb' b' >>~. fb
    Respond c  fc' -> Respond c (\c' -> fb' +>>. fc' c')
    M          m   -> M (m >>= \p' -> return (fb' +>>. p'))
    Pure       r   -> Pure r
{-# INLINABLE (+>>.) #-}

{- $reflect
    @(reflectSteppable .)@ transforms each streaming category into its dual:

    * The requestSteppable category is the dual of the respondSteppable category

@
'reflectSteppable' '.' 'respondSteppable' = 'requestSteppable'

'reflectSteppable' '.' (f '/>/.' g) = 'reflectSteppable' '.' f '/</.' 'reflectSteppable' '.' g
@

@
'reflectSteppable' '.' 'requestSteppable' = 'respondSteppable'

'reflectSteppable' '.' (f '\>\.' g) = 'reflectSteppable' '.' f '\<\.' 'reflectSteppable' '.' g
@

    * The pull category is the dual of the push category

@
'reflectSteppable' '.' 'pushSteppable' = 'pull'

'reflectSteppable' '.' (f '>~>.' g) = 'reflectSteppable' '.' f '<+<' 'reflectSteppable' '.' g
@

@
'reflectSteppable' '.' 'pull' = 'pushSteppable'

'reflectSteppable' '.' (f '>+>' g) = 'reflectSteppable' '.' f '<~<.' 'reflectSteppable' '.' g
@
-}

-- | Switch the upstream and downstream ends
reflectSteppable :: (Monad m) => ProxySteppable a' a b' b m r -> ProxySteppable b b' a a' m r
reflectSteppable = go
  where
    go p = case p of
        Request a' fa  -> Respond a' (\a  -> go (fa  a ))
        Respond b  fb' -> Request b  (\b' -> go (fb' b'))
        M          m   -> M (m >>= \p' -> return (go p'))
        Pure    r      -> Pure r
{-# INLINABLE reflectSteppable #-}

{-| An effect in the base monad

    'EffectSteppable's neither 'Pipes.await' nor 'Pipes.yield'
-}
type EffectSteppable = ProxySteppable Void () () Void

-- | 'ProducerSteppable's can only 'Pipes.yield'
type ProducerSteppable b = ProxySteppable Void () () b

-- | 'PipeSteppable's can both 'Pipes.await' and 'Pipes.yield'
type PipeSteppable a b = ProxySteppable () a () b

-- | 'ConsumerSteppable's can only 'Pipes.await'
type ConsumerSteppable a = ProxySteppable () a () Void

{-| @ClientSteppable a' a@ sends requestSteppables of type @a'@ and receives responses of
    type @a@.

    'ClientSteppable's only 'requestSteppable' and never 'respondSteppable'.
-}
type ClientSteppable a' a = ProxySteppable a' a () Void

{-| @ServerSteppable b' b@ receives requestSteppables of type @b'@ and sends responses of type
    @b@.

    'ServerSteppable's only 'respondSteppable' and never 'requestSteppable'.
-}
type ServerSteppable b' b = ProxySteppable Void () b' b

-- | Like 'EffectSteppable', but with a polymorphic type
type EffectSteppable' m r = forall x' x y' y . ProxySteppable x' x y' y m r

-- | Like 'ProducerSteppable', but with a polymorphic type
type ProducerSteppable' b m r = forall x' x . ProxySteppable x' x () b m r

-- | Like 'ConsumerSteppable', but with a polymorphic type
type ConsumerSteppable' a m r = forall y' y . ProxySteppable () a y' y m r

-- | Like 'ServerSteppable', but with a polymorphic type
type ServerSteppable' b' b m r = forall x' x . ProxySteppable x' x b' b m r

-- | Like 'ClientSteppable', but with a polymorphic type
type ClientSteppable' a' a m r = forall y' y . ProxySteppable a' a y' y m r

-- | Equivalent to ('/>/.') with the arguments flipped
(\<\.)
    :: (Monad m)
    => (b -> ProxySteppable x' x c' c m b')
    -- ^
    -> (a -> ProxySteppable x' x b' b m a')
    -- ^
    -> (a -> ProxySteppable x' x c' c m a')
    -- ^
p1 \<\. p2 = p2 />/. p1
{-# INLINABLE (\<\.) #-}

-- | Equivalent to ('\>\.') with the arguments flipped
(/</.)
    :: (Monad m)
    => (c' -> ProxySteppable b' b x' x m c)
    -- ^
    -> (b' -> ProxySteppable a' a x' x m b)
    -- ^
    -> (c' -> ProxySteppable a' a x' x m c)
    -- ^
p1 /</. p2 = p2 \>\. p1
{-# INLINABLE (/</.) #-}

-- | Equivalent to ('>~>.') with the arguments flipped
(<~<.)
    :: (Monad m)
    => (b -> ProxySteppable b' b c' c m r)
    -- ^
    -> (a -> ProxySteppable a' a b' b m r)
    -- ^
    -> (a -> ProxySteppable a' a c' c m r)
    -- ^
p1 <~<. p2 = p2 >~>. p1
{-# INLINABLE (<~<.) #-}

-- | Equivalent to ('>+>.') with the arguments flipped
(<+<.)
    :: (Monad m)
    => (c' -> ProxySteppable b' b c' c m r)
    -- ^
    -> (b' -> ProxySteppable a' a b' b m r)
    -- ^
    -> (c' -> ProxySteppable a' a c' c m r)
    -- ^
p1 <+<. p2 = p2 >+>. p1
{-# INLINABLE (<+<.) #-}

-- | Equivalent to ('//>.') with the arguments flipped
(<\\.)
    :: (Monad m)
    => (b -> ProxySteppable x' x c' c m b')
    -- ^
    ->       ProxySteppable x' x b' b m a'
    -- ^
    ->       ProxySteppable x' x c' c m a'
    -- ^
f <\\. p = p //>. f
{-# INLINABLE (<\\.) #-}

-- | Equivalent to ('>\\') with the arguments flipped
(//<.)
    :: (Monad m)
    =>        ProxySteppable b' b y' y m c
    -- ^
    -> (b' -> ProxySteppable a' a y' y m b)
    -- ^
    ->        ProxySteppable a' a y' y m c
    -- ^
p //<. f = f >\\. p
{-# INLINABLE (//<.) #-}

-- | Equivalent to ('>>~.') with the arguments flipped
(~<<.)
    :: (Monad m)
    => (b  -> ProxySteppable b' b c' c m r)
    -- ^
    ->        ProxySteppable a' a b' b m r
    -- ^
    ->        ProxySteppable a' a c' c m r
    -- ^
k ~<<. p = p >>~. k
{-# INLINABLE (~<<.) #-}

-- | Equivalent to ('+>>.') with the arguments flipped
(<<+.)
    :: (Monad m)
    =>         ProxySteppable b' b c' c m r
    -- ^
    -> (b'  -> ProxySteppable a' a b' b m r)
    -- ^
    ->         ProxySteppable a' a c' c m r
    -- ^
k <<+. p = p +>>. k
{-# INLINABLE (<<+.) #-}
