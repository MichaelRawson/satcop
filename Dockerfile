FROM centos:centos7
ENV PATH="/root/.cargo/bin:${PATH}"
ENV RUSTFLAGS='-L /'
ENV CARGO_PROFILE_RELEASE_LTO=fat
ENV CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
ENV CARGO_PROFILE_RELEASE_DEBUG=0
ENV CARGO_PROFILE_RELEASE_PANIC="abort"
RUN yum -y install gcc
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y 
COPY Cargo.toml /Cargo.toml
COPY Cargo.lock /Cargo.lock
COPY libpicosat.a /libpicosat.a
COPY src /src
RUN cargo update
RUN cargo build --release