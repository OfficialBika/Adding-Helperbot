"""Runtime migration layer checks."""

import inspect


def test_runtime_helpers_are_async():
    from migration.app_runtime import initialize_runtime, close_runtime

    assert inspect.iscoroutinefunction(initialize_runtime)
    assert inspect.iscoroutinefunction(close_runtime)
