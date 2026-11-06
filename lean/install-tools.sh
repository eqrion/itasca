#!/bin/sh
# Called by `just tools`; source builds stay outside the project checkout.
set -eu

tools_dir=$1
aeneas_rev=$2
rust_toolchain=$3
opam_switch=$4

# Fail before cloning or compiling if the OCaml environment is not ready.
opam exec --switch="$opam_switch" -- dune --version > /dev/null

checkout() {
    repo_url=$1
    repo_dir=$2
    repo_rev=$3
    if [ ! -d "$repo_dir" ]; then
        git clone --no-checkout "$repo_url" "$repo_dir"
        git -C "$repo_dir" checkout --detach "$repo_rev"
    fi
    if [ -n "$(git -C "$repo_dir" status --porcelain --untracked-files=normal)" ]; then
        echo "Refusing to build modified sources in $repo_dir" >&2
        exit 1
    fi
    git -C "$repo_dir" checkout --detach "$repo_rev"
}

mkdir -p "$tools_dir"
checkout https://github.com/AeneasVerif/aeneas.git "$tools_dir/source" "$aeneas_rev"
charon_rev=$(tail -n 1 "$tools_dir/source/charon-pin")
checkout https://github.com/AeneasVerif/charon.git "$tools_dir/source/charon" "$charon_rev"

(
    cd "$tools_dir/source/charon/charon"
    RUSTUP_TOOLCHAIN=$rust_toolchain cargo build --release --locked --bin charon --bin charon-driver
)
make -C "$tools_dir/source/charon" charon-ml/src/CharonVersion.ml
(
    cd "$tools_dir/source/src"
    opam exec --switch="$opam_switch" -- dune build main.exe
)
mkdir -p "$tools_dir/bin"
cp "$tools_dir/source/src/_build/default/main.exe" "$tools_dir/bin/aeneas"
cp "$tools_dir/source/charon/charon/target/release/charon" "$tools_dir/bin/charon"
cp "$tools_dir/source/charon/charon/target/release/charon-driver" "$tools_dir/bin/charon-driver"
printf 'Installed Aeneas %s and Charon %s in %s/bin\n' "$aeneas_rev" "$charon_rev" "$tools_dir"
