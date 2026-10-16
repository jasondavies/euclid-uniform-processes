"""Print the local, self-contained HTML paper using Playwright Chromium."""
from pathlib import Path
from playwright.sync_api import sync_playwright

root = Path(__file__).resolve().parents[1]
with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1000, 'height': 1400})
    page.goto((root / 'paper/short-gcd-certificates.html').as_uri())
    assert page.locator('.citation').evaluate_all(
        '(nodes) => nodes.every(n => n.textContent.trim().length > 0)')
    page.pdf(path=str(root / 'paper/short-gcd-certificates.pdf'),
             print_background=True, prefer_css_page_size=True)
    page.screenshot(path='/tmp/gcd-paper.png', full_page=False)
    print(f'Rendered {page.locator("math").count()} formulae and '
          f'{page.locator(".citation").count()} citations.')
    browser.close()
