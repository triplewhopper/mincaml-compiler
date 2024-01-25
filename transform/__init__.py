import contextlib
import logging
from collections.abc import MutableMapping

from bounds import Bounds

logging.basicConfig(level=logging.INFO, format='%(name)s - %(levelname)s - %(message)s')


class CustomAdapter(logging.LoggerAdapter[logging.Logger]):
    def process(self, msg: str, kwargs: MutableMapping[str, object]):
        bounds = (self.extra or {}).get('bounds')
        assert isinstance(bounds, Bounds)
        return bounds.dump_with(msg), kwargs


def bind_logger(*, logger: logging.Logger):
    assert isinstance(logger, logging.Logger)
    adapter = CustomAdapter(logger)

    @contextlib.contextmanager
    def get_adapter(bounds: Bounds | None = None):
        assert isinstance(bounds, Bounds) or bounds is None
        if bounds is None:
            yield adapter
            return
        extra, adapter.extra = adapter.extra, {'bounds': bounds}
        try:
            yield adapter
        finally:
            adapter.extra = extra

    return get_adapter
