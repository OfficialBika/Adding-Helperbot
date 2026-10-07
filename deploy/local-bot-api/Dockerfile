FROM ubuntu:24.04 AS build

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
RUN git clone --recursive --depth 1 --branch ${TELEGRAM_BOT_API_REF} https://github.com/tdlib/telegram-bot-api.git

WORKDIR /src/telegram-bot-api
RUN cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
    && cmake --build build --target telegram-bot-api --parallel

FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        libssl3t64 \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --uid 1000 --gid 1000 --create-home --shell /usr/sbin/nologin botapi \
    && mkdir -p /var/lib/telegram-bot-api/temp \
    && chown -R 1000:1000 /var/lib/telegram-bot-api

COPY --from=build /src/telegram-bot-api/build/telegram-bot-api /usr/local/bin/telegram-bot-api

USER 1000:1000
EXPOSE 8081

HEALTHCHECK --interval=15s --timeout=3s --start-period=10s --retries=5 \
    CMD curl -sS --max-time 2 http://127.0.0.1:8081/ >/dev/null || exit 1

ENTRYPOINT ["/usr/local/bin/telegram-bot-api"]
