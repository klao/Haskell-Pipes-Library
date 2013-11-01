{-| This is an internal module, meaning that it is unsafe to import unless you
    understand the risks.

    This module provides a fast implementation by weakening the monad
    transformer laws.  These laws do not hold if you can pattern match on the
    constructors, as the following counter-example illustrates:

@
'lift' '.' 'return' = 'M' '.' 'return' '.' 'Pure'

'return' = 'Pure'

'lift' '.' 'return' /= 'return'
@

    You do not need to worry about this if you do not import this module, since
    the other modules in this library do not export the constructors or export
    any functions which can violate the monad transformer laws.
-}

{-# LANGUAGE
    FlexibleInstances
  , MultiParamTypeClasses
  , RankNTypes
  , UndecidableInstances
  , CPP
  #-}
module Pipes.Internal (
    -- * Church-encoded
    Proxy(..),
    unsafeHoist,
    -- * Manifested
    ProxySteppable(..),
    unsafeHoistSteppable,
    observeSteppable,
    -- * Conversion
    toProxySteppable,
    fromProxySteppable,
    ) where

import Control.Applicative (Applicative(pure, (<*>)), Alternative(empty, (<|>)))
import Control.Monad (liftM, MonadPlus(..))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans.Class (MonadTrans(lift))
import Control.Monad.Error (MonadError(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State (MonadState(..))
import Control.Monad.Writer (MonadWriter(..))
import Data.Monoid (mempty,mappend)

{-| A 'ProxySteppable' is the manifested 'Proxy' type.

    The type variables signify:

    * @a'@ and @a@ - The upstream interface, where @(a')@s go out and @(a)@s
      come in

    * @b'@ and @b@ - The downstream interface, where @(b)@s go out and @(b')@s
      come in

    * @m @ - The base monad

    * @r @ - The return value
-}
data ProxySteppable a' a b' b m r
    = Request a' (a  -> ProxySteppable a' a b' b m r )
    | Respond b  (b' -> ProxySteppable a' a b' b m r )
    | M          (m    (ProxySteppable a' a b' b m r))
    | Pure    r

instance (Monad m) => Functor (ProxySteppable a' a b' b m) where
    fmap f p0 = go p0 where
        go p = case p of
            Request a' fa  -> Request a' (\a  -> go (fa  a ))
            Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
            M          m   -> M (m >>= \p' -> return (go p'))
            Pure    r      -> Pure (f r)

instance (Monad m) => Applicative (ProxySteppable a' a b' b m) where
    pure      = Pure
    pf <*> px = go pf where
        go p = case p of
            Request a' fa  -> Request a' (\a  -> go (fa  a ))
            Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
            M          m   -> M (m >>= \p' -> return (go p'))
            Pure     f     -> fmap f px

instance (Monad m) => Monad (ProxySteppable a' a b' b m) where
    return = Pure
    (>>=)  = _bind

_bind
    :: (Monad m)
    => ProxySteppable a' a b' b m r
    -> (r -> ProxySteppable a' a b' b m r')
    -> ProxySteppable a' a b' b m r'
p0 `_bind` f = go p0 where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        M          m   -> M (m >>= \p' -> return (go p'))
        Pure     r     -> f r

{-# RULES
    "_bind (Request a' k) f" forall a' k f .
        _bind (Request a' k) f = Request a' (\a  -> _bind (k a)  f);
    "_bind (Respond b  k) f" forall b  k f .
        _bind (Respond b  k) f = Respond b  (\b' -> _bind (k b') f);
    "_bind (M          m) f" forall m    f .
        _bind (M          m) f = M (m >>= \p -> return (_bind p f));
    "_bind (Pure    r   ) f" forall r    f .
        _bind (Pure    r   ) f = f r;
  #-}

instance MonadTrans (ProxySteppable a' a b' b) where
    lift m = M (m >>= \r -> return (Pure r))

{-| 'unsafeHoist' is like 'hoist', but faster.

    This is labeled as unsafe because you will break the monad transformer laws
    if you do not pass a monad morphism as the first argument.  This function is
    safe if you pass a monad morphism as the first argument.
-}
unsafeHoistSteppable
    :: (Monad m)
    => (forall x . m x -> n x) -> ProxySteppable a' a b' b m r -> ProxySteppable a' a b' b n r
unsafeHoistSteppable nat = go
  where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        M          m   -> M (nat (m >>= \p' -> return (go p')))
        Pure       r   -> Pure r

instance MFunctor (ProxySteppable a' a b' b) where
    hoist nat p0 = go (observeSteppable p0) where
        go p = case p of
            Request a' fa  -> Request a' (\a  -> go (fa  a ))
            Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
            M          m   -> M (nat (m >>= \p' -> return (go p')))
            Pure       r   -> Pure r

instance (MonadIO m) => MonadIO (ProxySteppable a' a b' b m) where
    liftIO m = M (liftIO (m >>= \r -> return (Pure r)))

instance (MonadReader r m) => MonadReader r (ProxySteppable a' a b' b m) where
    ask = lift ask
    local f = go
        where
          go p = case p of
              Request a' fa  -> Request a' (\a  -> go (fa  a ))
              Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
              Pure    r      -> Pure r
              M       m      -> M (go `liftM` local f m)
#if MIN_VERSION_mtl(2,1,0)
    reader = lift . reader
#else
#endif

instance (MonadState s m) => MonadState s (ProxySteppable a' a b' b m) where
    get = lift get
    put = lift . put
#if MIN_VERSION_mtl(2,1,0)
    state = lift . state
#else
#endif

instance (MonadWriter w m) => MonadWriter w (ProxySteppable a' a b' b m) where
#if MIN_VERSION_mtl(2,1,0)
    writer = lift . writer
#else
#endif
    tell = lift . tell
    listen proxy = go proxy mempty
        where
          go p w = case p of
              Request a' fa  -> Request a' (\a  -> go (fa  a ) w)
              Respond b  fb' -> Respond b  (\b' -> go (fb' b') w)
              Pure    r      -> Pure (r, w)
              M       m      -> M (
                (\(p', w') -> go p' $! mappend w w') `liftM` listen m)

    pass = go
        where
          go p = case p of
              Request a' fa  -> Request a' (\a  -> go (fa  a ))
              Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
              M       m      -> M (go `liftM` m)
              Pure    (r, f) -> M (pass (return (Pure r, f)))

instance (MonadError e m) => MonadError e (ProxySteppable a' a b' b m) where
    throwError = lift . throwError
    catchError p0 f = go p0
      where
        go p = case p of
            Request a' fa  -> Request a' (\a  -> go (fa  a ))
            Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
            Pure    r      -> Pure r
            M          m   -> M ((do
                p' <- m
                return (go p') ) `catchError` (\e -> return (f e)) )

instance (MonadPlus m) => Alternative (ProxySteppable a' a b' b m) where
    empty = mzero
    (<|>) = mplus

instance (MonadPlus m) => MonadPlus (ProxySteppable a' a b' b m) where
    mzero = lift mzero
    mplus p0 p1 = go p0
      where
        go p = case p of
            Request a' fa  -> Request a' (\a  -> go (fa  a ))
            Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
            Pure    r      -> Pure r
            M          m   -> M ((do
                p' <- m
                return (go p') ) `mplus` return p1 )

{-| The monad transformer laws are correct when viewed through the 'observe'
    function:

@
'observe' ('lift' ('return' r)) = 'observe' ('return' r)

'observe' ('lift' (m '>>=' f)) = 'observe' ('lift' m '>>=' 'lift' '.' f)
@

    This correctness comes at a small cost to performance, so use this function
    sparingly.

    This function is a convenience for low-level @pipes@ implementers.  You do
    not need to use 'observe' if you stick to the safe API.
-}
observeSteppable :: (Monad m) => ProxySteppable a' a b' b m r -> ProxySteppable a' a b' b m r
observeSteppable p0 = M (go p0) where
    go p = case p of
        Request a' fa  -> return (Request a' (\a  -> observeSteppable (fa  a )))
        Respond b  fb' -> return (Respond b  (\b' -> observeSteppable (fb' b')))
        M          m'  -> m' >>= go
        Pure    r      -> return (Pure r)
{-# INLINABLE observeSteppable #-}

--------------------------------------------------------------------------------

{-| The Church-encoded 'Proxy'. -}

newtype Proxy a' a b' b m r =  Proxy
    { unProxy
        :: forall x
        .  (a' -> (a  -> x) -> x)
        -> (b  -> (b' -> x) -> x)
        -> (           m x  -> x)
        -> (             r  -> x)
        -> x
    }

instance (Monad m) => Functor (Proxy a' a b' b m) where
    {-# INLINABLE fmap #-}
    fmap f p =
        Proxy (\request' respond' lift' pure' ->
            unProxy p request' respond' lift' (pure' . f))

instance (Monad m) => Monad (Proxy a' a b' b m) where
    {-# INLINABLE return #-}
    return r = Proxy (\_ _ _ pure' -> pure' r)
    {-# INLINABLE (>>=) #-}
    m >>= f  =
        Proxy (\request' respond' lift' pure' ->
            unProxy m request' respond' lift' (\r ->
                unProxy (f r) request' respond' lift' pure'))

instance MonadTrans (Proxy a' a b' b) where
    {-# INLINABLE lift #-}
    lift m = Proxy (\_ _ lift' pure' ->
        lift' (m >>= \r -> return (pure' r)))

unsafeHoist
    :: (Monad m)
    => (forall x . m x -> n x) -> Proxy a' a b' b m r -> Proxy a' a b' b n r
unsafeHoist nat p = Proxy (\request' respond' lift' pure' ->
        unProxy p request' respond' (lift' . nat) pure')
{-# INLINABLE unsafeHoist #-}

-- This is the 'unsafeHoist' and we need some kind of observe here too, right?
instance MFunctor (Proxy a' a b' b) where
    {-# INLINABLE hoist #-}
    hoist nat p = Proxy (\request' respond' lift' pure' ->
        unProxy p request' respond' (lift' . nat) pure')

instance (MonadIO m) => MonadIO (Proxy a' a b' b m) where
    {-# INLINE liftIO #-}
    liftIO m = lift (liftIO m)


toProxySteppable :: Proxy a' a b' b m r -> ProxySteppable a' a b' b m r
toProxySteppable p = unProxy p Request Respond M Pure
{-# INLINE CONLIKE [1] toProxySteppable #-}

fromProxySteppable :: (Monad m) => ProxySteppable a' a b' b m r -> Proxy a' a b' b m r
fromProxySteppable p0 = Proxy proxy
  where
    proxy request' respond' lift' pure' = go p0
      where
        go p = case p of
            Request a' fa  -> request' a' (go . fa )
            Respond b  fb' -> respond' b  (go . fb')
            M fp           -> lift' (liftM go fp)
            Pure r         -> pure' r
{-# INLINABLE [1] fromProxySteppable #-}

{-# RULES
    "toProxySteppable (fromProxySteppable p)" forall p .
        toProxySteppable (fromProxySteppable p) = p;
    "fromProxySteppable (toProxySteppable p)" forall p .
        fromProxySteppable (toProxySteppable p) = p;
  #-}
