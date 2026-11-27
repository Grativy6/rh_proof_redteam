const fs = require("node:fs");
const path = require("node:path");
const { pathToFileURL } = require("node:url");
const assert = require("node:assert/strict");
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || "playwright");

(async () => {
  const pagePath = path.resolve(process.argv[2]);
  const target = path.resolve(process.argv[3]);
  fs.mkdirSync(target, { recursive: true });
  const browser = await chromium.launch({
    headless: true,
    executablePath: process.env.CARRY_BROWSER || "C:/Program Files/Google/Chrome/Application/chrome.exe"
  });
  try {
    const context = await browser.newContext({viewport:{width:1100,height:970}});
    await context.setOffline(true);
    const page = await context.newPage();
    const errors = [];
    const external = [];
    page.on("pageerror", err => errors.push(err.message));
    page.on("request", req => {
      if (/^https?:/.test(req.url())) external.push(req.url());
    });
    await page.goto(pathToFileURL(pagePath).href);
    assert.equal(await page.locator("#high").innerText(), "1262");
    assert.equal(await page.locator("#low").innerText(), "3273344365508751233");
    assert.match(await page.locator("#square-status").innerText(), /5\^32/);
    await page.locator("#leave").click();
    assert.equal(await page.locator("#passed").innerText(), "3273344365508751233");
    await page.locator('[data-example="twin"]').click();
    assert.equal(await page.locator("#passed").innerText(), "17");
    assert.equal(await page.locator("#remainder").innerText(), "2");
    await page.locator("#keep").click();
    assert.equal(await page.locator("#remainder").innerText(), "0");
    await page.locator('[data-example="released"]').click();
    await page.locator("#leave").click();
    assert.equal(await page.locator("#passed").innerText(), "586678051033346049");
    assert.equal(await page.locator("#remainder").innerText(), "0");
    await page.locator("#widen").click();
    assert.equal(await page.locator("#bits").inputValue(), "385");
    assert.equal(await page.locator("#high").innerText(), "0");
    await page.locator("#number").fill("-1");
    assert.match(await page.locator("#error").innerText(), /whole number/);
    await page.locator('[data-example="spill"]').click();
    await page.locator("#bits").fill("64");
    await page.locator("#keep").click();
    await page.screenshot({path:path.join(target,"desktop.png"),fullPage:true});
    await page.setViewportSize({width:390,height:844});
    await page.screenshot({path:path.join(target,"mobile.png"),fullPage:true});
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await page.locator("#reset").click();
    await page.locator("#next").click();
    assert.match(await page.locator("#squares tr").last().innerText(), /5\^2/);
    assert.deepEqual(errors, []);
    assert.deepEqual(external, []);
    const receipt = {page:pagePath,checks:"split, restore, prime/composite reading, wider word, invalid input, squaring, narrow layout",networkRequests:external.length,browserErrors:errors,offline:true};
    fs.writeFileSync(path.join(target,"result.json"),JSON.stringify(receipt,null,2)+"\n");
    process.stdout.write(JSON.stringify(receipt)+"\n");
  } finally {
    await browser.close();
  }
})().catch(err => { process.stderr.write(err.stack+"\n"); process.exitCode=1; });