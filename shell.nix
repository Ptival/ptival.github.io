{ nixpkgs ? import <nixpkgs> {} }:
nixpkgs.stdenv.mkDerivation {
  buildInputs = (with nixpkgs; [
    jekyll
    #rake
    #ruby
  ]);
  name = "ptival.github.io";
  shellHook = ''
    export NIXSHELL="$NIXSHELL\[ptival.github.io\]"
    export SSL_CERT_FILE="/etc/ssl/certs/ca-bundle.crt"
  '';
}
