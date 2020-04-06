---
layout: post
title: "My current Nix setup for Haskell development (April 2020)"
date: 2020-04-02 12:00:00 +0100
permalink: nix-haskell-setup
comments: true
categories:
---

I have recently encountered [this blog
post](https://medium.com/purely-functional/nix-setup-for-haskell-with-ghcide-and-hlint-3e268343efed)
describing a great way of setting up your Haskell development environment under
Nix.  While I found it illuminating, I do not like the setup as it is there, so
I went ahead and modified it some.  Here are the reasons why, and the how.

Requirements
------------

One thing I really appreciated from that blog post was understanding how you can
build a local Hoogle for your dependencies.  I also really like the idea of
pinning the Nix packages revision for the project, independent from the nix
packages you use: I can now update my system without worrying about incurring a
rebuild of my shell (though using lorri alleviates this too!).

One thing I did not like about the setup from that blog post is the duplication
of logic in different projects.  I'd like to write the logic for building my
programming environment in one place, and benefit from it in my projects.  For
this, I have found it useful to use NUR, the Nix user repository mechanism,
which will do while we wait for Nix flakes to be widely used!

With this, I have defined a set of NUR library functions that can be called in
my projects to build Haskell development environments as I like them.  The other
requirements are:

- each project should be able to choose its GHC version,

- because I am still waiting on haskell-language-server to be polished, I am
  still using intero, so I also need to build Nix shells for stack, and would
  like to avoid repetition between setting up my development shell and stack's
  shell,

- every Haskell dependency should be overridable, since I often use versions
  that are not the one currently in nixpkgs, or even versions that are not on
  Hackage.

Nix library functions for building my shells
--------------------------------------------

The first step of the process consists in building the proper GHC with the
proper dependencies installed, along with their Hoogle documentation.  Because
this should be shared between my development shell and stack's shell, I isolate
the process in a function `computeHaskellSetup`.  It currently takes three knobs
as input: `nixpkgsRev` specifies the nixpkgs commit to be used (so as to set in
stone the environment unless I manually bump the revision), `nixpkgsArgs` are
the arguments that will be passed to nixpkgs upon importing them (in practice,
I'm only using it to pass overlays, but I'm allowing it to have additional
options if necessary), and `pkg` is a description of the package that this shell
is built for (basically, information for `callCabal2nix`).

{% highlight nix %}
  computeHaskellSetup =
    { ghcVersion
    , nixpkgsRev
    , nixpkgsArgs # typically, a Haskell overlay
    , pkg         # arguments to callCabal2nix
    }:
    let

      pkgs = import (builtins.fetchGit {
        url = "https://github.com/NixOS/nixpkgs.git";
        rev = nixpkgsRev;
      }) nixpkgsArgs;

      hsPkgs = pkgs.haskell.packages.${ghcVersion};

      pkgDrv = callCabal2nixGitignore pkgs pkg.name pkg.path pkg.args;

      pkgDeps = pkgDrv.getBuildInputs.haskellBuildInputs;

      ghc = hsPkgs.ghcWithHoogle (_: pkgDeps);

    in
      {
        inherit
          ghc
          hsPkgs
          pkgs
        ;
      };
{% endhighlight %}

We build `pkgs`, the instantiation of nixpkgs, by picking the selected revision
and passing around the overlays.  Then, we grab the set `hsPkgs` of Haskell
packages for the GHC version `ghcVersion`: while it looks like the vanilla set
from nixpkgs, remember that there might be overlays at play that will tweak what
packages are present.

`pkgDrv` is the derivation for the package we are trying to work on.  It uses
another of my library functions, `callCabal2nixGitignore` (implementation
[here](https://github.com/Ptival/nur-packages/blob/409d3c420e9eed67ccb006293fb0a884d8c7f5d6/lib/default.nix#L5-L10)),
which works just like `callCabal2nix`, except that it will filter out files in
your development directory that are not meant to be part of the source.  This
will avoid the usual problem of having your `.stack-work`, your `dist-newstyle`,
or even your Nix expressions end up in the derivation, making it both larger
than it needs be, and triggering spurious environment rebuilds when these files
change.

Then we grab the dependencies of this package, `pkgDeps`, and create a `ghc` set
up with Hoogle documentation for those packages.  This function simply returns a
set containing `ghc`, `hsPkgs`, and `pkgs`, to be consumed by either the
function for building the development shell, or the function for building the
stack shell.

Building the development shell
------------------------------

To build the development shell, we want to call the gool old `mkShell` with the
proper build inputs.  It suffices to compute the setup from the last section,
and grab the packages we want, here, I choose to always have `cabal-install`,
`ghc`, `ghcide`, `hlint`, and `stack`.

Note that I grab the `ghc` from `setup` rather than from `hsPkgs`, as it is the
one we have set up to have Hoogle documentation: once in your Nix shell, you can
run `hoogle server`, then navigate to localhost:8080 and have a Hoogle with
exactly those packages your project depends on.

As for the `NIX_GHC_LIBDIR` variable, it needs to be set for `ghcide` to known
where to find the proper `ghc`.  Otherwise, it will complain about `package not
found` a lot since it'll be likely reaching a different `ghc`.

{% highlight nix %}
  haskellDevShell =
    { ghcVersion
    , nixpkgsRev
    , nixpkgsArgs # typically, a Haskell overlay
    , pkg         # arguments to callCabal2nix
    }:
    let
      setup = computeHaskellSetup { inherit ghcVersion nixpkgsRev nixpkgsArgs pkg; };
    in

      setup.pkgs.mkShell {

        buildInputs = with setup.hsPkgs; [
          cabal-install
          setup.ghc     # NOTE: this is the one with Hoogle set up
          ghcide
          hlint
          stack
        ];

        NIX_GHC_LIBDIR = "${setup.ghc}/lib/ghc-${setup.ghc.version}";

      };
{% endhighlight %}

Building the stack shell
------------------------

Stack users under nix have two choices: either you can rely on stack for
building its own nix shell, possibly listing some packages you'd like to be
included:

{% highlight yaml %}
nix:
  enable: true
  packages:
    - zlib
{% endhighlight %}

or you can have it build the shell you tell it to, giving you more control:

{% highlight yaml %}
nix:
  enable: true
  shell-file: stack-shell.nix
{% endhighlight %}

Said nix expression must accept an argument named `ghc` that will be passed by
stack to be the GHC of choice.  Due to how stack works, it does not benefit from
the Nix-built Haskell packages, and will build its own copies of everything.  As
such, making a stack shell is fairly disconnected to what we've done so far.
All it needs to do is describe what packages should be available within the
shell, since stack builds and executes your package in a pure environment.
When your package is an executable, it might rely on having other libraries or
executable present at run-time, and so you need to make these available, so that
running `stack run my-executable` will be able to see those libraries and other
executables.

{% highlight nix %}
  stackShell =
    { ghcVersion
    , mkBuildInputs
    , nixpkgsRev
    , nixpkgsArgs # typically, a Haskell overlay
    , pkg         # arguments to callCabal2nix
    }:
    let
      setup = computeHaskellSetup { inherit ghcVersion nixpkgsRev nixpkgsArgs pkg; };
    in
      pkgs.haskell.lib.buildStackProject {

        # grab the correct GHC without Hoogle support since stack does not need it
        ghc = setup.pkgs.haskell.compiler.${ghcVersion};

        inherit (pkg) name;

        buildInputs = mkBuildInputs setup.pkgs setup.hsPkgs;

      };
{% endhighlight %}

This function barely uses what comes out of `setup` since stack does its own
thing with Haskell packages.  All I do is inherit the vanilla version of GHC,
and call `mkBuildInputs` to create the `buildInputs` field, passing it the
proper `pkgs` and `hsPkgs` it should use.

If your `stack` complains that it does not know how to install GHC for your
system, it means there is a mismatch between the GHC version declared in the
`ghcVersion` field of your config, and the GHC version corresponding to the
resolver in your `stack.yaml`.  Make sure that they agree on which GHC version
they expect.

Using the library
-----------------

My setups include three files:

- `config.nix` defines the inputs to `computeHaskellSetup`,
- `shell.nix` calls `haskellDevShell`,
- `stack-shell.nix` calls `stackShell`.

Here is an example `config.nix`:

{% highlight nix %}
{ nur ? (import <nixpkgs> {}).nur.repos.ptival
}:
rec {

  ghcVersion = "ghc882";

  advent-of-code-overlay = self: super:
    let

      dontCheck = super.haskell.lib.dontCheck;

    in
      {
        haskell = super.haskell // {
          inherit ghcVersion;
          packages = super.haskell.packages // {
            "${ghcVersion}" = super.haskell.packages.${ghcVersion}.extend (selfH: superH: {

                # Here is how you get a given version of a package if it is published on Hackage
                ghc-tcplugins-extra = selfH.callHackage "ghc-tcplugins-extra" "0.3.2" {};

                # Here is how you disable the test-suite for a package that breaks during them
                monad-dijkstra = dontCheck superH.monad-dijkstra;

                # Here is how you get an arbitrary commit of an arbitrary Haskell package from source.
                # Since it comes from GitHub, no need for `callCabal2nixGitignore` as the source comes
                # from a fresh checkout, `callCabal2nix` suffices.
                polysemy =
                  (selfH.callCabal2nix
                    "polysemy"
                    (builtins.fetchGit {
                      url = "https://github.com/polysemy-research/polysemy.git";
                      rev = "016c16fbb1b57a0d728e57e2cf8e36453e8edd8d";
                    })
                    {});

            });

          };

        };

      };

  nixpkgsRev = "c2dcdea8c68631fc15ec837d0df7def2b66d0676";

  nixpkgsArgs = {
    overlays = [
      (nur.overlays.haskell-dev { inherit ghcVersion; })
      advent-of-code-overlay
    ];
  };

  pkg = {
    name = "advent-of-code";
    path = ./.;
    args = {};
  };

}
{% endhighlight %}

Nothing should be surprising here.  Note the different methods of overriding
packages, depending on whether you want some version published on Hackage, or
some bleeding-edge commit from some version control system.

As for `shell.nix`:

{% highlight nix %}
{ nur ? (import <nixpkgs> {}).nur.repos.ptival
}:
let
  config = import ./config.nix {};
  haskell-dev-overlay = nur.overlays.haskell-dev.${config.ghcVersion};
in
nur.lib.haskellDevShell {

  inherit (config) ghcVersion nixpkgsRev pkg;

  nixpkgsArgs = {
    overlays = [
      haskell-dev-overlay
      config.advent-of-code-overlay
    ];
  };

}
{% endhighlight %}

It imports `config.nix` and passes in two overlays: the overlay from my package,
as defined in `config.nix`, and my Haskell development overlay, which is also
hosted on NUR, and is fairly involved, so [here is a link to
it](https://github.com/Ptival/nur-packages/blob/409d3c420e9eed67ccb006293fb0a884d8c7f5d6/overlays/haskell-dev/default.nix).
It has one field per GHC version, and for each version, it tweaks packages like
`ghcide` to pick a version that is compatible with that GHC.

Finally, `stack-shell.nix`:

{% highlight nix %}
{ nur ? (import <nixpkgs> {}).nur.repos.ptival
}:
let
  config = import ./config.nix {};
in
nur.lib.stackShell {

  inherit (config) ghcVersion nixpkgsRev pkg;

  mkBuildInputs = pkgs: hsPkgs: [
    pkgs.zlib
  ];

  nixpkgsArgs = {
    overlays = [
      config.advent-of-code-overlay
    ];
  };

}
{% endhighlight %}

As you can see, the repetition is minimized by also importing `config.nix`.
Note that I only use the package overlay, and not the development overlay, since
stack does not need access to my development packages.  However, note the
additional `mkBuildInputs` field, that lets me make some packages available
within the pure stack shell, for instance, `zlib` here.  This corresponds to
packages you'd put in the `packages` list of your `stack.yaml`, and should have
all the run-time dependencies of your executables and test suites.

I hope this helped you improve your setup!  [Let me
know](https://github.com/Ptival) if you improve on this setup, I'm always
looking for nicer ways of dealing with setting up my programming environment.
