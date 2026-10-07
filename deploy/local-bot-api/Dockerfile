# Build the official Telegram Bot API server from source.
# Ref can be pinned to a specific commit for reproducible production builds.
FROM ubuntu:24.04 AS builder

ARG DEBIAN_FRONTEND=noninteractive
ARG TELEGRAM_BOT_API_REF=master

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        git \
        g++ \
        cmake \
        make \
        pkg-config \
        libssl-dev \
        zlib1g-dev \
        gperf \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src

RUN git clone --recursive https://github.com/tdlib/telegram-bot-api.git . \
    && git checkout "${TELEGRAM_BOT_API_REF}" \
    && git submodule update --init --recursive \
    && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
    && cmake --build build --target install -j"$(nproc)"

FROM ubuntu:24.04 AS runtime

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        libssl3t64 \
        zlib1g \
        curl \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /var/lib/telegram-bot-api/temp

COPY --from=builder /usr/local/bin/telegram-bot-api /usr/local/bin/telegram-bot-api

EXPOSE 8081

HEALTHCHECK --interval=15s --timeout=3s --start-period=20s --retries=5 \
  CMD-SHELL 'timeout 3 bash -c "</dev/tcp/127.0.0.1/8081"' || exit 1

ENTRYPOINT ["/usr/local/bin/telegram-bot-api"]
CMD [
  "--local",
  "--dir=/var/lib/telegram-bot-api",
  "--temp-dir=/var/lib/telegram-bot-api/temp",
  "--http-port=8081",
  "--verbosity=1"
]
